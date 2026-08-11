/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauTightness
import UniformEquilibrium.Quitting.Punishment.Floor

/-!
# Time disintegration of plateau deviation laws

The terminal law used by the semantic-plateau argument forgets when its
selected atom occurred.  This module restores that chronology on the same
actual deviated profile.  A finite terminal atom is the sum of the exact
survival-weighted product-action atoms at the live rows; `Never` is exactly
the residual live mass.

For a deterministic pure-time deviation the formula separates further:
coalitions excluding the deviator occur before its selected stop, while
coalitions containing it occur exactly at that stop.  This is the literal
`before / at / infinity` split requested by the plateau capstone.  The final
results deliberately stop short of identifying these actual rows with exact
minimum-semantic prefix rows; that incidence is the remaining strategic
coupling premise.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Exact stage atoms -/

/-- The unique Boolean action whose quitter set is the displayed terminal
coalition. -/
def quittingTerminalCoalitionAction
    (terminal : {S : Finset ι // S.Nonempty}) : ι → Bool :=
  fun who => decide (who ∈ terminal.val)

@[simp] theorem quittingQuitters_terminalCoalitionAction
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingQuitters (quittingTerminalCoalitionAction terminal) = terminal.val := by
  ext who
  simp [quittingQuitters, quittingTerminalCoalitionAction]

@[simp] theorem quittingTerminalCoalitionAction_mk_quitters
    (action : ι → Bool) (hnonempty : (quittingQuitters action).Nonempty) :
    quittingTerminalCoalitionAction
        (⟨quittingQuitters action, hnonempty⟩ :
          {S : Finset ι // S.Nonempty}) = action := by
  funext who
  cases haction : action who <;>
    simp [quittingTerminalCoalitionAction, quittingQuitters, haction]

/-- Conditional product-law mass of a coalition at the canonical live row. -/
def quittingLiveRowCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) : ℝ :=
  (((quittingGame reward).stageActionDist profile
      (quittingLiveHist reward time))
    (quittingTerminalCoalitionAction terminal)).toReal

/-- Unconditional probability of reaching a live row and absorbing there at
the displayed coalition. -/
def quittingStageCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) : ℝ :=
  quittingLiveMass reward profile time *
    quittingLiveRowCoalitionMass reward profile time terminal

theorem quittingLiveRowCoalitionMass_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    0 ≤ quittingLiveRowCoalitionMass reward profile time terminal :=
  ENNReal.toReal_nonneg

theorem quittingStageCoalitionMass_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    0 ≤ quittingStageCoalitionMass reward profile time terminal :=
  mul_nonneg (quittingLiveMass_nonneg reward profile time)
    (quittingLiveRowCoalitionMass_nonneg reward profile time terminal)

omit [DecidableEq ι] in
@[simp] theorem quittingAbsorbedMass_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingAbsorbedMass reward profile 0 terminal = 0 := by
  unfold quittingAbsorbedMass StochasticGame.expectedStateValue
  rw [(quittingGame reward).histDist_zero, expect_pure]
  change quittingAbsorbedIndicator reward terminal none = 0
  simp [quittingAbsorbedIndicator]

/-- Exact one-step absorption recurrence for one terminal coalition. -/
theorem quittingAbsorbedMass_succ_eq_add_stageCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingAbsorbedMass reward profile (time + 1) terminal =
      quittingAbsorbedMass reward profile time terminal +
        quittingStageCoalitionMass reward profile time terminal := by
  classical
  letI : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  letI : ∀ player : ι, Finite ((quittingGame reward).Act player) :=
    fun _ => inferInstanceAs (Finite Bool)
  unfold quittingAbsorbedMass
  rw [(quittingGame reward).expectedStateValue_succ]
  calc
    expect ((quittingGame reward).histDist profile none time) (fun history =>
        expect ((quittingGame reward).stageActionDist profile history)
          (fun action => expect
            ((quittingGame reward).transition history.2 action)
              (quittingAbsorbedIndicator reward terminal))) =
      expect ((quittingGame reward).histDist profile none time) (fun history =>
        quittingAbsorbedIndicator reward terminal history.2 +
          quittingLiveRowCoalitionMass reward profile time terminal *
            quittingLiveIndicator reward history.2) := by
        apply Math.ProbabilityMassFunction.expect_congr_on_support
        intro history hsupported
        cases hstate : history.2 with
        | none =>
            have heq :=
              eq_quittingLiveHist_of_mem_support_histDist_of_snd_eq_none
                reward profile history hsupported hstate
            subst history
            rw [show quittingAbsorbedIndicator reward terminal none = 0 by
              simp [quittingAbsorbedIndicator]]
            simp only [zero_add, quittingLiveIndicator_none, mul_one]
            unfold quittingLiveRowCoalitionMass
            rw [Math.Probability.apply_toReal_eq_expect_indicator]
            apply congrArg
              (expect ((quittingGame reward).stageActionDist profile
                (quittingLiveHist reward time)))
            funext action
            by_cases haction :
                action = quittingTerminalCoalitionAction terminal
            · subst action
              rw [if_pos rfl]
              have hnonempty :
                  (quittingQuitters
                    (quittingTerminalCoalitionAction terminal)).Nonempty := by
                rw [quittingQuitters_terminalCoalitionAction]
                exact terminal.property
              rw [quittingGame_transition_none, dif_pos (by
                simpa [quittingQuitters] using hnonempty)]
              change expect (PMF.pure (some
                (⟨quittingQuitters
                    (quittingTerminalCoalitionAction terminal), hnonempty⟩ :
                  {S : Finset ι // S.Nonempty})))
                    (quittingAbsorbedIndicator reward terminal) = 1
              simp [quittingAbsorbedIndicator]
            · rw [if_neg haction]
              by_cases hnonempty : (quittingQuitters action).Nonempty
              · rw [quittingGame_transition_none, dif_pos (by
                  simpa [quittingQuitters] using hnonempty)]
                have hterminal :
                    (⟨quittingQuitters action, hnonempty⟩ :
                        {S : Finset ι // S.Nonempty}) ≠ terminal := by
                  intro heq
                  apply haction
                  calc
                    action = quittingTerminalCoalitionAction
                        (⟨quittingQuitters action, hnonempty⟩ :
                          {S : Finset ι // S.Nonempty}) :=
                      (quittingTerminalCoalitionAction_mk_quitters
                        action hnonempty).symm
                    _ = quittingTerminalCoalitionAction terminal := by
                      rw [heq]
                change expect (PMF.pure (some
                  (⟨quittingQuitters action, hnonempty⟩ :
                    {S : Finset ι // S.Nonempty})))
                      (quittingAbsorbedIndicator reward terminal) = 0
                rw [expect_pure]
                unfold quittingAbsorbedIndicator
                rw [if_neg]
                intro heq
                exact hterminal (Option.some.inj heq)
              · rw [quittingGame_transition_none, dif_neg (by
                  simpa [quittingQuitters] using hnonempty)]
                simp [quittingAbsorbedIndicator]
        | some absorbed =>
            by_cases heq : absorbed = terminal
            · subst absorbed
              simp [quittingGame, quittingAbsorbedIndicator,
                quittingLiveIndicator]
            · simp [quittingGame, quittingAbsorbedIndicator,
                quittingLiveIndicator, heq]
    _ = quittingAbsorbedMass reward profile time terminal +
        quittingLiveRowCoalitionMass reward profile time terminal *
          quittingLiveMass reward profile time := by
      rw [expect_add, expect_const_mul,
        quittingLiveMass_eq_expectedStateValue]
      rfl
    _ = quittingAbsorbedMass reward profile time terminal +
        quittingStageCoalitionMass reward profile time terminal := by
      rw [quittingStageCoalitionMass]
      ring

/-- Finite time disintegration into chronological stage atoms. -/
theorem quittingAbsorbedMass_eq_sum_stageCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) : ∀ cutoff : ℕ,
    quittingAbsorbedMass reward profile cutoff terminal =
      ∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward profile time terminal := by
  intro cutoff
  induction cutoff with
  | zero => simp
  | succ cutoff ih =>
      rw [quittingAbsorbedMass_succ_eq_add_stageCoalitionMass,
        Finset.sum_range_succ, ih]

/-- Infinite disintegration of one terminal-coalition mass. -/
theorem hasSum_quittingStageCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) :
    HasSum (fun time => quittingStageCoalitionMass reward profile time terminal)
      (quittingAbsorbedMassLimit reward profile terminal) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun time => quittingStageCoalitionMass_nonneg reward profile time terminal)]
  simpa only [← quittingAbsorbedMass_eq_sum_stageCoalitionMass] using
    tendsto_quittingAbsorbedMass reward profile terminal

theorem tsum_quittingStageCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) :
    ∑' time, quittingStageCoalitionMass reward profile time terminal =
      quittingAbsorbedMassLimit reward profile terminal :=
  (hasSum_quittingStageCoalitionMass reward profile terminal).tsum_eq

/-- Complete terminal-law disintegration: Never is the live boundary and a
finite coalition is the sum of its chronological stage atoms. -/
theorem quittingTerminalOutcomeMass_eq_timeDisintegration
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (outcome : QuittingTerminalOutcome ι) :
    quittingTerminalOutcomeMass reward profile outcome =
      match outcome with
      | none => quittingLiveMassLimit reward profile
      | some terminal =>
          ∑' time, quittingStageCoalitionMass reward profile time terminal := by
  cases outcome with
  | none => rfl
  | some terminal =>
      simpa [quittingTerminalOutcomeMass] using
        (tsum_quittingStageCoalitionMass reward profile terminal).symm

/-! ## Pure-time before / at / infinity split -/

theorem quittingLiveRowCoalitionMass_update_pureTime_eq_zero_of_self_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (quitTime : Option ℕ) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty})
    (hzero : (quittingPureTimeHazard quitTime time
      (quittingTerminalCoalitionAction terminal who)) = 0) :
    quittingLiveRowCoalitionMass reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who quitTime))
        time terminal = 0 := by
  unfold quittingLiveRowCoalitionMass StochasticGame.stageActionDist
  change ((pmfPi (fun player =>
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who quitTime)) player time
          (quittingLiveHist reward time)))
      (quittingTerminalCoalitionAction terminal)).toReal = 0
  rw [pmfPi_apply]
  have hproduct :
      (∏ player, (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who quitTime)) player time
          (quittingLiveHist reward time)
          (quittingTerminalCoalitionAction terminal player)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ who)
    rw [Function.update_self]
    change quittingPureTimeHazard quitTime time
      (quittingTerminalCoalitionAction terminal who) = 0
    exact hzero
  rw [hproduct]
  rfl

theorem quittingStageCoalitionMass_update_pureTime_eq_zero_of_self_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (quitTime : Option ℕ) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty})
    (hzero : (quittingPureTimeHazard quitTime time
      (quittingTerminalCoalitionAction terminal who)) = 0) :
    quittingStageCoalitionMass reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who quitTime))
        time terminal = 0 := by
  rw [quittingStageCoalitionMass,
    quittingLiveRowCoalitionMass_update_pureTime_eq_zero_of_self_zero
      reward profile who quitTime time terminal hzero, mul_zero]

/-- Once a finite pure stop has occurred, no live mass remains. -/
theorem quittingLiveMass_update_pureTime_some_eq_zero_of_stop_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    {quitTime cutoff : ℕ} (hlt : quitTime < cutoff) :
    quittingLiveMass reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who (some quitTime)))
        cutoff = 0 := by
  let deviated := Function.update profile who
    (quittingPureTimeBehaviorStrategy reward who (some quitTime))
  have hcontinue : quittingJointContinueMass reward deviated quitTime = 0 := by
    unfold quittingJointContinueMass StochasticGame.stageActionDist
    change ((pmfPi (fun player => deviated player quitTime
        (quittingLiveHist reward quitTime)))
      (quittingAllContinueAction : ι → Bool)).toReal = 0
    rw [pmfPi_apply]
    have hproduct :
        (∏ player, deviated player quitTime
          (quittingLiveHist reward quitTime)
          (quittingAllContinueAction player)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ who)
      rw [show deviated who quitTime (quittingLiveHist reward quitTime) =
          PMF.pure true by
        simp [deviated, quittingPureTimeBehaviorStrategy]]
      change (PMF.pure true) false = 0
      rw [PMF.pure_apply]
      norm_num
    rw [hproduct]
    rfl
  have hstop : quittingLiveMass reward deviated (quitTime + 1) = 0 := by
    rw [quittingLiveMass_succ, hcontinue, mul_zero]
  exact le_antisymm
    ((quittingLiveMass_antitone reward deviated
      (by omega : quitTime + 1 ≤ cutoff)).trans_eq hstop)
    (quittingLiveMass_nonneg reward deviated cutoff)

theorem quittingStageCoalitionMass_update_pureTime_some_eq_zero_of_stop_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    {quitTime time : ℕ} (hlt : quitTime < time)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who (some quitTime)))
        time terminal = 0 := by
  rw [quittingStageCoalitionMass,
    quittingLiveMass_update_pureTime_some_eq_zero_of_stop_lt
      reward profile who hlt, zero_mul]

theorem quittingAbsorbedMassLimit_eq_absorbedMass_of_stage_zero_after
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) (cutoff : ℕ)
    (hzero : ∀ time, cutoff ≤ time →
      quittingStageCoalitionMass reward profile time terminal = 0) :
    quittingAbsorbedMassLimit reward profile terminal =
      quittingAbsorbedMass reward profile cutoff terminal := by
  have hconst : ∀ time, cutoff ≤ time →
      quittingAbsorbedMass reward profile time terminal =
        quittingAbsorbedMass reward profile cutoff terminal := by
    intro time htime
    induction time, htime using Nat.le_induction with
    | base => rfl
    | succ time hcutoff ih =>
        rw [quittingAbsorbedMass_succ_eq_add_stageCoalitionMass,
          hzero time hcutoff, add_zero, ih]
  apply tendsto_nhds_unique (tendsto_quittingAbsorbedMass reward profile terminal)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop cutoff] with time htime
  exact (hconst time htime).symm

/-- A pure finite stop disintegrates every coalition excluding the deviator
into the exact sum of the survival-weighted atoms strictly before the stop. -/
theorem quittingTerminalOutcomeMass_update_pureTime_some_notMem_eq_before
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (quitTime : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (hnot : who ∉ terminal.val) :
    quittingTerminalOutcomeMass reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who (some quitTime)))
        (some terminal) =
      ∑ time ∈ Finset.range quitTime,
        quittingStageCoalitionMass reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who (some quitTime)))
          time terminal := by
  let deviated := Function.update profile who
    (quittingPureTimeBehaviorStrategy reward who (some quitTime))
  have hat : quittingStageCoalitionMass reward deviated quitTime terminal = 0 := by
    apply quittingStageCoalitionMass_update_pureTime_eq_zero_of_self_zero
      reward profile who (some quitTime) quitTime terminal
    simp [quittingTerminalCoalitionAction, hnot]
  have hafter : ∀ time, quitTime ≤ time →
      quittingStageCoalitionMass reward deviated time terminal = 0 := by
    intro time htime
    rcases htime.eq_or_lt with rfl | hlt
    · exact hat
    · exact quittingStageCoalitionMass_update_pureTime_some_eq_zero_of_stop_lt
        reward profile who hlt terminal
  change quittingAbsorbedMassLimit reward deviated terminal = _
  rw [quittingAbsorbedMassLimit_eq_absorbedMass_of_stage_zero_after
    reward deviated terminal quitTime hafter]
  exact quittingAbsorbedMass_eq_sum_stageCoalitionMass
    reward deviated terminal quitTime

/-- A coalition containing the deviator can occur under a finite pure stop
only at the selected stop itself. -/
theorem quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (quitTime : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (hmem : who ∈ terminal.val) :
    quittingTerminalOutcomeMass reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who (some quitTime)))
        (some terminal) =
      quittingStageCoalitionMass reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who (some quitTime)))
        quitTime terminal := by
  let deviated := Function.update profile who
    (quittingPureTimeBehaviorStrategy reward who (some quitTime))
  have hbefore : ∀ time, time < quitTime →
      quittingStageCoalitionMass reward deviated time terminal = 0 := by
    intro time htime
    apply quittingStageCoalitionMass_update_pureTime_eq_zero_of_self_zero
      reward profile who (some quitTime) time terminal
    rw [quittingPureTimeHazard_some_of_ne (by omega : time ≠ quitTime)]
    simp [quittingTerminalCoalitionAction, hmem]
  have hprefix : quittingAbsorbedMass reward deviated quitTime terminal = 0 := by
    rw [quittingAbsorbedMass_eq_sum_stageCoalitionMass]
    apply Finset.sum_eq_zero
    intro time htime
    exact hbefore time (Finset.mem_range.mp htime)
  have hafter : ∀ time, quitTime + 1 ≤ time →
      quittingStageCoalitionMass reward deviated time terminal = 0 := by
    intro time htime
    exact quittingStageCoalitionMass_update_pureTime_some_eq_zero_of_stop_lt
      reward profile who (by omega) terminal
  change quittingAbsorbedMassLimit reward deviated terminal = _
  rw [quittingAbsorbedMassLimit_eq_absorbedMass_of_stage_zero_after
    reward deviated terminal (quitTime + 1) hafter,
    quittingAbsorbedMass_succ_eq_add_stageCoalitionMass, hprefix, zero_add]

/-- Under the pure `Never` deviation, no terminal coalition containing the
deviator has positive mass. -/
theorem quittingTerminalOutcomeMass_update_pureTime_none_mem_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (terminal : {S : Finset ι // S.Nonempty})
    (hmem : who ∈ terminal.val) :
    quittingTerminalOutcomeMass reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who none))
        (some terminal) = 0 := by
  change quittingAbsorbedMassLimit reward _ terminal = 0
  rw [← tsum_quittingStageCoalitionMass]
  have hall : (fun time => quittingStageCoalitionMass reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who none)) time terminal) =
      (fun _ => 0) := by
    funext time
    apply quittingStageCoalitionMass_update_pureTime_eq_zero_of_self_zero
      reward profile who none time terminal
    simp [quittingTerminalCoalitionAction, hmem]
  rw [hall]
  simp

/-! ## Local support versus diffuse charge -/

/-- Positive mass on one marked stage coalition exposes every member of that
coalition in the support of its actual live-row marginal.  For an opponent of
the pure-time deviator, this is support in the original base profile. -/
theorem positive_base_liveQuit_of_positive_pureTime_stageCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who other : ι)
    (quitTime : Option ℕ) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty})
    (hother : other ∈ terminal.val) (hne : other ≠ who)
    (hpositive : 0 < quittingStageCoalitionMass reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who quitTime))
      time terminal) :
    0 < (profile other time (quittingLiveHist reward time) true).toReal := by
  letI : ∀ player : ι, Finite ((quittingGame reward).Act player) :=
    fun _ => inferInstanceAs (Finite Bool)
  let deviated := Function.update profile who
    (quittingPureTimeBehaviorStrategy reward who quitTime)
  have hlive : 0 ≤ quittingLiveMass reward deviated time :=
    quittingLiveMass_nonneg reward deviated time
  have hrow : 0 < quittingLiveRowCoalitionMass reward deviated time terminal := by
    have hrowNonneg :=
      quittingLiveRowCoalitionMass_nonneg reward deviated time terminal
    unfold quittingStageCoalitionMass at hpositive
    nlinarith
  have hactionMass :
      0 < (((quittingGame reward).stageActionDist deviated
        (quittingLiveHist reward time))
          (quittingTerminalCoalitionAction terminal)).toReal := hrow
  have hactionNe :
      ((quittingGame reward).stageActionDist deviated
        (quittingLiveHist reward time))
          (quittingTerminalCoalitionAction terminal) ≠ 0 := by
    intro hzero
    rw [hzero] at hactionMass
    simp at hactionMass
  have hactionSupport : quittingTerminalCoalitionAction terminal ∈
      ((quittingGame reward).stageActionDist deviated
        (quittingLiveHist reward time)).support :=
    (PMF.mem_support_iff _ _).2 hactionNe
  have hcoord := (quittingGame reward).coord_mem_support_stageActionDist
    deviated (quittingLiveHist reward time) hactionSupport other
  have hactionOther : quittingTerminalCoalitionAction terminal other = true := by
    simp [quittingTerminalCoalitionAction, hother]
  rw [hactionOther] at hcoord
  have hbase : deviated other time (quittingLiveHist reward time) =
      profile other time (quittingLiveHist reward time) := by
    simp [deviated, Function.update_of_ne hne]
  rw [hbase] at hcoord
  exact ENNReal.toReal_pos ((PMF.mem_support_iff _ _).1 hcoord)
    (PMF.apply_ne_top _ _)

/-- A positive collision atom at the selected stop exposes a distinct
opponent with positive actual live-row Quit probability. -/
theorem exists_other_positive_base_liveQuit_of_positive_collisionAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (quitTime : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (hmem : who ∈ terminal.val) (hne : terminal.val ≠ {who})
    (hpositive : 0 < quittingTerminalOutcomeMass reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who (some quitTime)))
      (some terminal)) :
    ∃ other, other ≠ who ∧ other ∈ terminal.val ∧
      0 < (profile other quitTime
        (quittingLiveHist reward quitTime) true).toReal := by
  have hexists : ∃ other, other ∈ terminal.val ∧ other ≠ who := by
    by_contra hnot
    push Not at hnot
    apply hne
    ext player
    constructor
    · intro hp
      simp [hnot player hp]
    · intro hp
      have heq : player = who := Finset.mem_singleton.mp hp
      simpa [heq] using hmem
  obtain ⟨other, hother, hotherNe⟩ := hexists
  refine ⟨other, hotherNe, hother, ?_⟩
  apply positive_base_liveQuit_of_positive_pureTime_stageCoalitionMass
    reward profile who other (some quitTime) quitTime terminal hother hotherNe
  rw [← quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
    reward profile who quitTime terminal hmem]
  exact hpositive

/-- Positive mass on one before-stop waiting atom likewise exposes a genuine
opponent Quit marginal in the actual base row. -/
theorem exists_other_positive_base_liveQuit_of_positive_waitingStageAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (quitTime : Option ℕ) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty})
    (hnot : who ∉ terminal.val)
    (hpositive : 0 < quittingStageCoalitionMass reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who quitTime))
      time terminal) :
    ∃ other, other ≠ who ∧ other ∈ terminal.val ∧
      0 < (profile other time (quittingLiveHist reward time) true).toReal := by
  obtain ⟨other, hother⟩ := terminal.property
  have hotherNe : other ≠ who := by
    intro heq
    exact hnot (heq ▸ hother)
  refine ⟨other, hotherNe, hother, ?_⟩
  exact positive_base_liveQuit_of_positive_pureTime_stageCoalitionMass
    reward profile who other quitTime time terminal hother hotherNe hpositive

/-- At any requested resolution, a positive finite before-stop charge either
contains one stage coalition atom of that size or is genuinely diffuse at
that resolution while retaining the whole positive aggregate charge. -/
theorem exists_concentratedAtom_or_diffuse_beforeCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (cutoff : ℕ) (lower resolution : ℝ)
    (hlower : lower < ∑ time ∈ Finset.range cutoff,
      quittingStageCoalitionMass reward profile time terminal) :
    (∃ time < cutoff,
        resolution ≤ quittingStageCoalitionMass reward profile time terminal) ∨
      (lower < ∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward profile time terminal ∧
        ∀ time < cutoff,
          quittingStageCoalitionMass reward profile time terminal < resolution) := by
  by_cases hresolution : ∃ time < cutoff,
      resolution ≤ quittingStageCoalitionMass reward profile time terminal
  · exact Or.inl hresolution
  · right
    refine ⟨hlower, ?_⟩
    push Not at hresolution
    exact hresolution

/-- The same concentration/diffuse split for an infinite waiting horizon. -/
theorem exists_concentratedAtom_or_diffuse_infiniteCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (lower resolution : ℝ)
    (hlower : lower < ∑' time,
      quittingStageCoalitionMass reward profile time terminal) :
    (∃ time,
        resolution ≤ quittingStageCoalitionMass reward profile time terminal) ∨
      (lower < ∑' time,
          quittingStageCoalitionMass reward profile time terminal ∧
        ∀ time,
          quittingStageCoalitionMass reward profile time terminal < resolution) := by
  by_cases hresolution : ∃ time,
      resolution ≤ quittingStageCoalitionMass reward profile time terminal
  · exact Or.inl hresolution
  · right
    refine ⟨hlower, ?_⟩
    push Not at hresolution
    exact hresolution

/-- **Exact marked concentration/diffuse/boundary alternative.**  Every
positive terminal atom of one actual pure-time deviation is exactly one of:

* a literal `Never` boundary with the chosen deviation equal to `none`;
* an at-stop collision atom, with a distinct opponent in actual local support
  whenever the coalition is not the deviator's singleton;
* a before-stop waiting charge, finite or infinite, which at every scale is
  either locally concentrated or diffuse while retaining its total mass.

The statement is intentionally profile-owned.  It does not assert that the
exposed live row is an exact minimum-semantic prefix row. -/
theorem positive_pureTime_terminalAtom_timeAlternative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (quitTime : Option ℕ) (outcome : QuittingTerminalOutcome ι)
    (resolution : ℝ)
    (hpositive : 0 < quittingTerminalOutcomeMass reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who quitTime)) outcome) :
    (outcome = none ∧ quitTime = none ∧
        0 < quittingLiveMassLimit reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who none))) ∨
      (∃ time terminal,
        quitTime = some time ∧ outcome = some terminal ∧
        who ∈ terminal.val ∧
        quittingTerminalOutcomeMass reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who quitTime)) outcome =
          quittingStageCoalitionMass reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who quitTime))
            time terminal ∧
        0 < quittingStageCoalitionMass reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who quitTime))
          time terminal) ∨
      (∃ terminal,
        outcome = some terminal ∧ who ∉ terminal.val ∧
        ((∃ time, quitTime = some time ∧
            quittingTerminalOutcomeMass reward
              (Function.update profile who
                (quittingPureTimeBehaviorStrategy reward who quitTime)) outcome =
              ∑ stage ∈ Finset.range time,
                quittingStageCoalitionMass reward
                  (Function.update profile who
                    (quittingPureTimeBehaviorStrategy reward who quitTime))
                  stage terminal ∧
            ((∃ stage < time, resolution ≤ quittingStageCoalitionMass reward
                (Function.update profile who
                  (quittingPureTimeBehaviorStrategy reward who quitTime))
                stage terminal) ∨
              (0 < ∑ stage ∈ Finset.range time,
                  quittingStageCoalitionMass reward
                    (Function.update profile who
                      (quittingPureTimeBehaviorStrategy reward who quitTime))
                    stage terminal ∧
                ∀ stage < time, quittingStageCoalitionMass reward
                  (Function.update profile who
                    (quittingPureTimeBehaviorStrategy reward who quitTime))
                  stage terminal < resolution))) ∨
          (quitTime = none ∧
            quittingTerminalOutcomeMass reward
              (Function.update profile who
                (quittingPureTimeBehaviorStrategy reward who quitTime)) outcome =
              ∑' stage, quittingStageCoalitionMass reward
                (Function.update profile who
                  (quittingPureTimeBehaviorStrategy reward who quitTime))
                stage terminal ∧
            ((∃ stage, resolution ≤ quittingStageCoalitionMass reward
                (Function.update profile who
                  (quittingPureTimeBehaviorStrategy reward who quitTime))
                stage terminal) ∨
              (0 < ∑' stage, quittingStageCoalitionMass reward
                  (Function.update profile who
                    (quittingPureTimeBehaviorStrategy reward who quitTime))
                  stage terminal ∧
                ∀ stage, quittingStageCoalitionMass reward
                  (Function.update profile who
                    (quittingPureTimeBehaviorStrategy reward who quitTime))
                  stage terminal < resolution))))) := by
  cases outcome with
  | none =>
      have hnever : quitTime = none := by
        cases hchoice : quitTime with
        | none => rfl
        | some time =>
            exfalso
            have hzero :=
              quittingLiveMassLimit_update_pureTimeBehaviorStrategy_some_eq_zero
                reward profile who time
            change 0 < quittingLiveMassLimit reward
              (Function.update profile who
                (quittingPureTimeBehaviorStrategy reward who quitTime)) at hpositive
            rw [hchoice, hzero] at hpositive
            exact lt_irrefl 0 hpositive
      subst quitTime
      left
      exact ⟨rfl, rfl, by
        simpa [quittingTerminalOutcomeMass] using hpositive⟩
  | some terminal =>
      by_cases hmem : who ∈ terminal.val
      · right
        left
        cases hchoice : quitTime with
        | none =>
            exfalso
            rw [hchoice,
              quittingTerminalOutcomeMass_update_pureTime_none_mem_eq_zero
                reward profile who terminal hmem] at hpositive
            exact lt_irrefl 0 hpositive
        | some time =>
            rw [hchoice] at hpositive
            refine ⟨time, terminal, rfl, rfl, hmem, ?_, ?_⟩
            · exact quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
                reward profile who time terminal hmem
            · rw [← quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
                reward profile who time terminal hmem]
              exact hpositive
      · right
        right
        refine ⟨terminal, rfl, hmem, ?_⟩
        cases hchoice : quitTime with
        | some time =>
            rw [hchoice] at hpositive
            left
            refine ⟨time, rfl, ?_, ?_⟩
            · exact
                quittingTerminalOutcomeMass_update_pureTime_some_notMem_eq_before
                  reward profile who time terminal hmem
            · have hsum : 0 < ∑ stage ∈ Finset.range time,
                  quittingStageCoalitionMass reward
                    (Function.update profile who
                      (quittingPureTimeBehaviorStrategy reward who (some time)))
                    stage terminal := by
                rw [←
                  quittingTerminalOutcomeMass_update_pureTime_some_notMem_eq_before
                    reward profile who time terminal hmem]
                exact hpositive
              exact exists_concentratedAtom_or_diffuse_beforeCharge reward
                (Function.update profile who
                  (quittingPureTimeBehaviorStrategy reward who (some time)))
                terminal time 0 resolution hsum
        | none =>
            rw [hchoice] at hpositive
            right
            refine ⟨rfl, ?_, ?_⟩
            · simpa [quittingTerminalOutcomeMass] using
                (tsum_quittingStageCoalitionMass reward
                  (Function.update profile who
                    (quittingPureTimeBehaviorStrategy reward who none))
                  terminal).symm
            · have hsum : 0 < ∑' stage, quittingStageCoalitionMass reward
                  (Function.update profile who
                    (quittingPureTimeBehaviorStrategy reward who none))
                  stage terminal := by
                rw [tsum_quittingStageCoalitionMass]
                exact hpositive
              exact exists_concentratedAtom_or_diffuse_infiniteCharge reward
                (Function.update profile who
                  (quittingPureTimeBehaviorStrategy reward who none))
                terminal 0 resolution hsum

end GameTheory
