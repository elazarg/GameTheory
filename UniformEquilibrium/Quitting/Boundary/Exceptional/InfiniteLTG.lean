/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Exceptional.TailLimits
import UniformEquilibrium.Quitting.Root.FirstBranch

/-!
# Infinite local-to-global bound for the exceptional quitting clock

This file closes the positive-survival branch directly for each unilateral
hazard sequence.  The finite exceptional `π`/`α` estimate controls the
surviving positive payoff gap at late live cutoffs.  A sub-Bellman telescope
then sends that boundary term to zero and charges the deviation only to the
summable weighted prescribed residuals.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Terminal payoff from the root sequence beginning at a supplied live
time. -/
def quittingRootSequenceTerminalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) : ℝ :=
  quittingTerminalPayoff reward
    (quittingRootSequenceProfile reward roots start) who

/-- Terminal payoff after replacing one player's root marginals by an
arbitrary time-dependent hazard sequence. -/
def quittingRootSequenceHazardTerminalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (start : ℕ) : ℝ :=
  quittingRootSequenceTerminalValue reward
    (quittingRootSequenceUpdate roots who hazard) who start

omit [DecidableEq ι] in
/-- A root-sequence profile is its current root followed by the root sequence
starting one live stage later. -/
theorem quittingRootSequenceProfile_eq_rootThenContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start : ℕ) :
    quittingRootSequenceProfile reward roots start =
      quittingRootThenContinuationProfile reward (roots start)
        (quittingRootSequenceProfile reward roots (start + 1)) := by
  funext player time history
  cases time with
  | zero => rfl
  | succ time =>
      simp [quittingRootSequenceProfile,
        quittingRootThenContinuationProfile, Nat.add_assoc]
      congr 2
      omega

omit [DecidableEq ι] in
/-- Terminal root-sequence values satisfy the exact prescribed root
recursion. -/
theorem quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) :
    quittingRootSequenceTerminalValue reward roots who start =
      quittingRootSuccessorPayoff reward
        (fun _ => quittingRootSequenceTerminalValue reward roots who
          (start + 1))
        (roots start) who := by
  classical
  rw [quittingRootSequenceTerminalValue,
    quittingRootSequenceProfile_eq_rootThenContinuation,
    quittingTerminalPayoff_rootThenContinuation_eq]
  unfold quittingRootSuccessorPayoff quittingRootExpectedPayoff
  apply congrArg (expect (pmfPi (roots start)))
  funext action
  by_cases hquit : (quittingQuitters action).Nonempty
  · simp [quittingRootPayoff, hquit]
  · simp [quittingRootPayoff, hquit, quittingRootSequenceTerminalValue]

omit [DecidableEq ι] in
/-- The terminal values prescribed by a root sequence form a genuine live
policy-evaluation sequence. -/
theorem isQuittingLivePrescribedValue_quittingRootSequenceTerminalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    IsQuittingLivePrescribedValue reward roots who
      (quittingRootSequenceTerminalValue reward roots who) :=
  quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff reward roots who

/-- The finite prescribed root recursion converges to the corresponding
root-sequence terminal value. -/
theorem tendsto_quittingFiniteRootPayoff_self_terminalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) :
    Tendsto (fun fuel => quittingFiniteRootPayoff reward roots who
      (fun time => roots time who) start fuel) atTop
      (nhds (quittingRootSequenceTerminalValue reward roots who start)) := by
  have hroots :
      quittingRootSequenceUpdate roots who (fun time => roots time who) =
        roots := by
    funext time
    exact Function.update_eq_self who (roots time)
  simpa only [quittingRootSequenceTerminalValue, hroots]
    using tendsto_quittingFiniteRootPayoff_terminal reward roots who
      (fun time => roots time who) start

/-- Finite one-step residuals select the terminal prescribed Bellman
residual at every fixed live time. -/
theorem tendsto_quittingFiniteRootOneStepResidual_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) :
    Tendsto (fun fuel => quittingFiniteRootOneStepResidual reward roots who
      (fun time => roots time who) start fuel) atTop
      (nhds (quittingPrescribedOneStepResidual reward roots who
        (quittingRootSequenceTerminalValue reward roots who) start)) := by
  have hnext := tendsto_quittingFiniteRootPayoff_self_terminalValue
    reward roots who (start + 1)
  have hcurrent :=
    (tendsto_quittingFiniteRootPayoff_self_terminalValue
      reward roots who start).comp (tendsto_add_atTop_nat 1)
  have hcontinue : Tendsto (fun fuel =>
      quittingFixedOpponentsContinueReward reward roots who start +
        quittingFixedOpponentsContinueMass roots who start *
          quittingFiniteRootPayoff reward roots who
            (fun time => roots time who) (start + 1) fuel) atTop
      (nhds (quittingFixedOpponentsContinueReward reward roots who start +
        quittingFixedOpponentsContinueMass roots who start *
          quittingRootSequenceTerminalValue reward roots who (start + 1))) :=
    tendsto_const_nhds.add
      (hnext.const_mul
        (quittingFixedOpponentsContinueMass roots who start))
  have hmaximum := (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
      quittingFixedOpponentsQuitValue reward roots who start) atTop
      (nhds (quittingFixedOpponentsQuitValue reward roots who start))).max
        hcontinue
  simpa only [quittingFiniteRootOneStepResidual,
    quittingPrescribedOneStepResidual, quittingLiveBellmanValue,
    Function.comp_apply] using hmaximum.sub hcurrent

/-- At a fixed live cutoff, every unilateral terminal hazard is controlled
by the selected terminal prescribed residual plus the conditional opponent
tail error.  This is the infinite-horizon form of the finite corrected
`π`/`α` estimate. -/
theorem quittingRootSequenceHazardTerminalGap_le_residual_add_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (deviation : ℕ → PMF Bool) (start : ℕ)
    (bound limit : ℝ) (hbound0 : 0 ≤ bound)
    (hreward : ∀ S, |reward S who| ≤ bound)
    (hsolo : 0 ≤ reward (quittingSingletonTerminal who) who)
    (hlimit : Tendsto
      (quittingOpponentSurvivalWeight roots who 0) atTop (nhds limit))
    (hlimitPos : 0 < limit) :
    quittingRootSequenceHazardTerminalValue reward roots who deviation start -
        quittingRootSequenceTerminalValue reward roots who start ≤
      quittingPrescribedOneStepResidual reward roots who
          (quittingRootSequenceTerminalValue reward roots who) start +
        4 * bound * (1 - limit /
          quittingOpponentSurvivalWeight roots who 0 start) := by
  have hdeviation :=
    (tendsto_quittingFiniteRootPayoff_terminal
      reward roots who deviation start).comp (tendsto_add_atTop_nat 1)
  have hprescribed :=
    (tendsto_quittingFiniteRootPayoff_self_terminalValue
      reward roots who start).comp (tendsto_add_atTop_nat 1)
  have hleft := hdeviation.sub hprescribed
  have hresidual := tendsto_quittingFiniteRootOneStepResidual_self
    reward roots who start
  have hsurvival :=
    (tendsto_quittingOpponentSurvivalWeight_tail
      roots who limit hlimit hlimitPos start).comp
        (tendsto_add_atTop_nat 1)
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have htail := (hone.sub hsurvival).const_mul (4 * bound)
  have hright := hresidual.add htail
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [] with fuel
  exact quittingFiniteRootPayoffGap_le_residual_add_exceptionalTail
    reward roots who (fun time => roots time who) deviation start fuel
      bound hbound0 hreward hsolo

/-- A unilateral hazard's terminal value is its current mixed root payoff
with the same hazard sequence continued one live stage later. -/
theorem quittingRootSequenceHazardTerminalValue_eq_rootExpectedPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (start : ℕ) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard start =
      quittingRootExpectedPayoff reward
        (fun _ => quittingRootSequenceHazardTerminalValue
          reward roots who hazard (start + 1))
        (Function.update (roots start) who (hazard start)) who := by
  unfold quittingRootSequenceHazardTerminalValue
  rw [quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff]
  rfl

/-- Every unilateral hazard's terminal value is a subsolution of the pure
Bellman maximum against the fixed opponent roots. -/
theorem quittingRootSequenceHazardTerminalValue_le_liveBellmanValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (time : ℕ) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard time ≤
      quittingLiveBellmanValue reward roots who
        (quittingRootSequenceHazardTerminalValue reward roots who hazard)
        time := by
  rw [quittingRootSequenceHazardTerminalValue_eq_rootExpectedPayoff,
    quittingRootExpectedPayoff_update_eq_endpointMix,
    quittingRootQuitPayoff_eq_fixedOpponentsQuitValue,
    quittingRootContinuePayoff_eq_fixedOpponents]
  let quitValue := quittingFixedOpponentsQuitValue reward roots who time
  let continueValue :=
    quittingFixedOpponentsContinueReward reward roots who time +
      quittingFixedOpponentsContinueMass roots who time *
        quittingRootSequenceHazardTerminalValue reward roots who hazard
          (time + 1)
  change
    (hazard time true).toReal * quitValue +
        (hazard time false).toReal * continueValue ≤
      max quitValue continueValue
  calc
    (hazard time true).toReal * quitValue +
          (hazard time false).toReal * continueValue ≤
        (hazard time true).toReal * max quitValue continueValue +
          (hazard time false).toReal * max quitValue continueValue := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left _ _) ENNReal.toReal_nonneg)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) ENNReal.toReal_nonneg)
    _ = max quitValue continueValue := by
      rw [← add_mul]
      have hmass : (hazard time true).toReal +
          (hazard time false).toReal = 1 := by
        linarith [quittingRoot_continueProbability_add_quitProbability
          (fun _ => hazard time) who]
      rw [hmass, one_mul]

/-- One sub-Bellman step for the positive deviation gap.  Taking the
positive part makes the iteration valid even when a particular deviation
is below the prescribed payoff at the next live time. -/
theorem quittingPositiveSubBellmanGap_le_residual_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed deviation : ℕ → ℝ) (time : ℕ)
    (hdeviation : deviation time ≤
      quittingLiveBellmanValue reward roots who deviation time)
    (hresidual : 0 ≤ quittingPrescribedOneStepResidual
      reward roots who prescribed time) :
    max (deviation time - prescribed time) 0 ≤
      quittingPrescribedOneStepResidual reward roots who prescribed time +
        quittingFixedOpponentsContinueMass roots who time *
          max (deviation (time + 1) - prescribed (time + 1)) 0 := by
  let quitValue := quittingFixedOpponentsQuitValue reward roots who time
  let prescribedContinue :=
    quittingFixedOpponentsContinueReward reward roots who time +
      quittingFixedOpponentsContinueMass roots who time *
        prescribed (time + 1)
  let deviationContinue :=
    quittingFixedOpponentsContinueReward reward roots who time +
      quittingFixedOpponentsContinueMass roots who time *
        deviation (time + 1)
  let continueMass := quittingFixedOpponentsContinueMass roots who time
  let nextGap := max (deviation (time + 1) - prescribed (time + 1)) 0
  have hmass0 : 0 ≤ continueMass := by
    exact quittingStationaryContinueMass_nonneg
      (Function.update (roots time) who (PMF.pure false))
  have hnext0 : 0 ≤ nextGap := le_max_right _ _
  have hnext : deviation (time + 1) - prescribed (time + 1) ≤ nextGap :=
    le_max_left _ _
  have hcontinue : deviationContinue ≤ prescribedContinue +
      continueMass * nextGap := by
    dsimp [deviationContinue, prescribedContinue, continueMass, nextGap]
    have := mul_le_mul_of_nonneg_left hnext hmass0
    linarith
  have hbonus0 : 0 ≤ continueMass * nextGap :=
    mul_nonneg hmass0 hnext0
  have hmaximum : max quitValue deviationContinue ≤
      max quitValue prescribedContinue + continueMass * nextGap := by
    apply max_le
    · exact (le_max_left quitValue prescribedContinue).trans
        (le_add_of_nonneg_right hbonus0)
    · calc
        deviationContinue ≤ prescribedContinue +
            continueMass * nextGap := hcontinue
        _ ≤ max quitValue prescribedContinue + continueMass * nextGap :=
          by linarith [le_max_right quitValue prescribedContinue]
  have hraw : deviation time - prescribed time ≤
      quittingPrescribedOneStepResidual reward roots who prescribed time +
        continueMass * nextGap := by
    dsimp [quittingLiveBellmanValue, quitValue, deviationContinue] at hdeviation
    dsimp [quittingPrescribedOneStepResidual, quittingLiveBellmanValue,
      quitValue, prescribedContinue, continueMass, nextGap]
    linarith
  apply max_le hraw
  exact add_nonneg hresidual hbonus0

/-- Finite weighted iteration of the positive sub-Bellman gap, retaining the
exact surviving terminal boundary. -/
theorem quittingPositiveSubBellmanGap_le_sum_residual_add_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed deviation : ℕ → ℝ)
    (hdeviation : ∀ time, deviation time ≤
      quittingLiveBellmanValue reward roots who deviation time)
    (hresidual : ∀ time, 0 ≤ quittingPrescribedOneStepResidual
      reward roots who prescribed time)
    (start fuel : ℕ) :
    max (deviation start - prescribed start) 0 ≤
      (∑ offset ∈ Finset.range fuel,
          quittingOpponentSurvivalWeight roots who start offset *
            quittingPrescribedOneStepResidual reward roots who prescribed
              (start + offset)) +
        quittingOpponentSurvivalWeight roots who start fuel *
          max (deviation (start + fuel) - prescribed (start + fuel)) 0 := by
  induction fuel with
  | zero =>
      simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      have hstep := quittingPositiveSubBellmanGap_le_residual_add
        reward roots who prescribed deviation (start + fuel)
          (hdeviation (start + fuel)) (hresidual (start + fuel))
      have hscaled := mul_le_mul_of_nonneg_left hstep
        (quittingOpponentSurvivalWeight_nonneg roots who start fuel)
      calc
        max (deviation start - prescribed start) 0 ≤
            (∑ offset ∈ Finset.range fuel,
                quittingOpponentSurvivalWeight roots who start offset *
                  quittingPrescribedOneStepResidual reward roots who prescribed
                    (start + offset)) +
              quittingOpponentSurvivalWeight roots who start fuel *
                max (deviation (start + fuel) -
                  prescribed (start + fuel)) 0 := ih
        _ ≤ (∑ offset ∈ Finset.range fuel,
                quittingOpponentSurvivalWeight roots who start offset *
                  quittingPrescribedOneStepResidual reward roots who prescribed
                    (start + offset)) +
              quittingOpponentSurvivalWeight roots who start fuel *
                (quittingPrescribedOneStepResidual reward roots who prescribed
                    (start + fuel) +
                  quittingFixedOpponentsContinueMass roots who (start + fuel) *
                    max (deviation (start + fuel + 1) -
                      prescribed (start + fuel + 1)) 0) := by
            exact add_le_add le_rfl hscaled
        _ = (∑ offset ∈ Finset.range (fuel + 1),
                quittingOpponentSurvivalWeight roots who start offset *
                  quittingPrescribedOneStepResidual reward roots who prescribed
                    (start + offset)) +
              quittingOpponentSurvivalWeight roots who start (fuel + 1) *
                max (deviation (start + (fuel + 1)) -
                  prescribed (start + (fuel + 1))) 0 := by
            rw [Finset.sum_range_succ,
              quittingOpponentSurvivalWeight_succ]
            simp only [Nat.add_assoc]
            ring

/-- Under finite weighted prescribed residual and positive exceptional
opponent survival, the positive terminal payoff gap of every fixed unilateral
hazard vanishes along late live cutoffs. -/
theorem tendsto_zero_quittingRootSequenceHazardTerminalPositiveGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (deviation : ℕ → PMF Bool)
    (bound limit : ℝ) (hbound0 : 0 ≤ bound)
    (hreward : ∀ S, |reward S who| ≤ bound)
    (hsolo : 0 ≤ reward (quittingSingletonTerminal who) who)
    (hlimit : Tendsto
      (quittingOpponentSurvivalWeight roots who 0) atTop (nhds limit))
    (hlimitPos : 0 < limit)
    (hsummable : Summable (fun time =>
      quittingOpponentSurvivalWeight roots who 0 time *
        quittingPrescribedOneStepResidual reward roots who
          (quittingRootSequenceTerminalValue reward roots who) time)) :
    Tendsto (fun time => max
      (quittingRootSequenceHazardTerminalValue reward roots who deviation time -
        quittingRootSequenceTerminalValue reward roots who time) 0)
      atTop (nhds 0) := by
  let residual : ℕ → ℝ := fun time =>
    quittingPrescribedOneStepResidual reward roots who
      (quittingRootSequenceTerminalValue reward roots who) time
  have hresidual0 : ∀ time, 0 ≤ residual time := fun time =>
    quittingPrescribedOneStepResidual_nonneg reward roots who
      (quittingRootSequenceTerminalValue reward roots who)
      (isQuittingLivePrescribedValue_quittingRootSequenceTerminalValue
        reward roots who) time
  have hresidualLimit : Tendsto residual atTop (nhds 0) :=
    tendsto_zero_of_summable_quittingOpponentSurvivalWeight_mul
      roots who limit residual hlimit hlimitPos hresidual0 hsummable
  have hratio := tendsto_quittingOpponentSurvivalLimitRatio_one
    roots who limit hlimit hlimitPos
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have herror : Tendsto (fun time =>
      residual time + 4 * bound *
        (1 - limit / quittingOpponentSurvivalWeight roots who 0 time))
      atTop (nhds 0) := by
    have htail := (hone.sub hratio).const_mul (4 * bound)
    simpa using hresidualLimit.add htail
  have herrorMax : Tendsto (fun time => max
      (residual time + 4 * bound *
        (1 - limit / quittingOpponentSurvivalWeight roots who 0 time)) 0)
      atTop (nhds 0) := by
    simpa using herror.max
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  apply squeeze_zero
  · intro time
    exact le_max_right _ _
  · intro time
    apply max_le_max_right
    simpa only [residual] using
      quittingRootSequenceHazardTerminalGap_le_residual_add_tail
        reward roots who deviation time bound limit hbound0 hreward hsolo
          hlimit hlimitPos
  · exact herrorMax

/-- **Exceptional infinite local-to-global theorem.**  If the opponents'
survival products have a positive limit and the nonnegative prescribed
Bellman residuals have finite weighted sum, then every time-dependent
unilateral hazard gains at most that total weighted residual. -/
theorem quittingRootSequenceHazardTerminalGap_le_tsum_residual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (deviation : ℕ → PMF Bool)
    (bound limit : ℝ) (hbound0 : 0 ≤ bound)
    (hreward : ∀ S, |reward S who| ≤ bound)
    (hsolo : 0 ≤ reward (quittingSingletonTerminal who) who)
    (hlimit : Tendsto
      (quittingOpponentSurvivalWeight roots who 0) atTop (nhds limit))
    (hlimitPos : 0 < limit)
    (hsummable : Summable (fun time =>
      quittingOpponentSurvivalWeight roots who 0 time *
        quittingPrescribedOneStepResidual reward roots who
          (quittingRootSequenceTerminalValue reward roots who) time)) :
    quittingRootSequenceHazardTerminalValue reward roots who deviation 0 -
        quittingRootSequenceTerminalValue reward roots who 0 ≤
      ∑' time, quittingOpponentSurvivalWeight roots who 0 time *
        quittingPrescribedOneStepResidual reward roots who
          (quittingRootSequenceTerminalValue reward roots who) time := by
  let prescribed := quittingRootSequenceTerminalValue reward roots who
  let deviationValue :=
    quittingRootSequenceHazardTerminalValue reward roots who deviation
  let residual : ℕ → ℝ := fun time =>
    quittingPrescribedOneStepResidual reward roots who prescribed time
  have hresidual0 : ∀ time, 0 ≤ residual time := fun time =>
    quittingPrescribedOneStepResidual_nonneg reward roots who prescribed
      (isQuittingLivePrescribedValue_quittingRootSequenceTerminalValue
        reward roots who) time
  have hdeviation : ∀ time, deviationValue time ≤
      quittingLiveBellmanValue reward roots who deviationValue time :=
    quittingRootSequenceHazardTerminalValue_le_liveBellmanValue
      reward roots who deviation
  have hfinite : ∀ fuel,
      deviationValue 0 - prescribed 0 ≤
        (∑ offset ∈ Finset.range fuel,
          quittingOpponentSurvivalWeight roots who 0 offset *
            residual offset) +
        quittingOpponentSurvivalWeight roots who 0 fuel *
          max (deviationValue fuel - prescribed fuel) 0 := by
    intro fuel
    exact (le_max_left (deviationValue 0 - prescribed 0) 0).trans
      (by
        simpa using
          (quittingPositiveSubBellmanGap_le_sum_residual_add_tail
            reward roots who prescribed deviationValue hdeviation hresidual0
              0 fuel))
  have hpartial : Tendsto (fun fuel =>
      ∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who 0 offset * residual offset)
      atTop (nhds (∑' time,
        quittingOpponentSurvivalWeight roots who 0 time * residual time)) :=
    hsummable.hasSum.tendsto_sum_nat
  have hpositiveGap : Tendsto (fun time =>
      max (deviationValue time - prescribed time) 0) atTop (nhds 0) := by
    simpa only [deviationValue, prescribed] using
      tendsto_zero_quittingRootSequenceHazardTerminalPositiveGap
        reward roots who deviation bound limit hbound0 hreward hsolo
          hlimit hlimitPos hsummable
  have hboundary : Tendsto (fun fuel =>
      quittingOpponentSurvivalWeight roots who 0 fuel *
        max (deviationValue fuel - prescribed fuel) 0) atTop (nhds 0) := by
    simpa using hlimit.mul hpositiveGap
  have hright := hpartial.add hboundary
  have hlimitBound : deviationValue 0 - prescribed 0 ≤
      (∑' time, quittingOpponentSurvivalWeight roots who 0 time *
        residual time) + 0 := by
    apply ge_of_tendsto' hright
    exact hfinite
  simpa only [deviationValue, prescribed, residual, add_zero] using hlimitBound

/-- Abstract terminal-boundary consumer for the positive sub-Bellman
telescope. -/
theorem quittingSubBellmanGap_le_tsum_residual_of_boundary_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed deviation : ℕ → ℝ)
    (hdeviation : ∀ time, deviation time ≤
      quittingLiveBellmanValue reward roots who deviation time)
    (hresidual : ∀ time, 0 ≤ quittingPrescribedOneStepResidual
      reward roots who prescribed time)
    (hsummable : Summable (fun time =>
      quittingOpponentSurvivalWeight roots who 0 time *
        quittingPrescribedOneStepResidual reward roots who prescribed time))
    (hboundary : Tendsto (fun fuel =>
      quittingOpponentSurvivalWeight roots who 0 fuel *
        max (deviation fuel - prescribed fuel) 0) atTop (nhds 0)) :
    deviation 0 - prescribed 0 ≤
      ∑' time, quittingOpponentSurvivalWeight roots who 0 time *
        quittingPrescribedOneStepResidual reward roots who prescribed time := by
  have hfinite : ∀ fuel,
      deviation 0 - prescribed 0 ≤
        (∑ offset ∈ Finset.range fuel,
          quittingOpponentSurvivalWeight roots who 0 offset *
            quittingPrescribedOneStepResidual reward roots who prescribed
              offset) +
        quittingOpponentSurvivalWeight roots who 0 fuel *
          max (deviation fuel - prescribed fuel) 0 := by
    intro fuel
    exact (le_max_left (deviation 0 - prescribed 0) 0).trans
      (by
        simpa using
          (quittingPositiveSubBellmanGap_le_sum_residual_add_tail
            reward roots who prescribed deviation hdeviation hresidual 0 fuel))
  have hpartial : Tendsto (fun fuel =>
      ∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who 0 offset *
          quittingPrescribedOneStepResidual reward roots who prescribed offset)
      atTop (nhds (∑' time,
        quittingOpponentSurvivalWeight roots who 0 time *
          quittingPrescribedOneStepResidual reward roots who prescribed time)) :=
    hsummable.hasSum.tendsto_sum_nat
  have hright := hpartial.add hboundary
  have hlimitBound : deviation 0 - prescribed 0 ≤
      (∑' time, quittingOpponentSurvivalWeight roots who 0 time *
        quittingPrescribedOneStepResidual reward roots who prescribed time) +
          0 := by
    apply ge_of_tendsto' hright
    exact hfinite
  simpa only [add_zero] using hlimitBound

/-- If the opponent-survival clock contracts to zero, bounded terminal
payoffs make the positive sub-Bellman boundary vanish, with no sign
condition on the player's singleton reward. -/
theorem quittingRootSequenceHazardTerminalGap_le_tsum_residual_of_survival_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (deviation : ℕ → PMF Bool) (bound : ℝ)
    (hbound0 : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hsurvival : Tendsto
      (quittingOpponentSurvivalWeight roots who 0) atTop (nhds 0))
    (hsummable : Summable (fun time =>
      quittingOpponentSurvivalWeight roots who 0 time *
        quittingPrescribedOneStepResidual reward roots who
          (quittingRootSequenceTerminalValue reward roots who) time)) :
    quittingRootSequenceHazardTerminalValue reward roots who deviation 0 -
        quittingRootSequenceTerminalValue reward roots who 0 ≤
      ∑' time, quittingOpponentSurvivalWeight roots who 0 time *
        quittingPrescribedOneStepResidual reward roots who
          (quittingRootSequenceTerminalValue reward roots who) time := by
  let prescribed := quittingRootSequenceTerminalValue reward roots who
  let deviationValue :=
    quittingRootSequenceHazardTerminalValue reward roots who deviation
  have hresidual : ∀ time, 0 ≤ quittingPrescribedOneStepResidual
      reward roots who prescribed time := fun time =>
    quittingPrescribedOneStepResidual_nonneg reward roots who prescribed
      (isQuittingLivePrescribedValue_quittingRootSequenceTerminalValue
        reward roots who) time
  have hdeviation : ∀ time, deviationValue time ≤
      quittingLiveBellmanValue reward roots who deviationValue time :=
    quittingRootSequenceHazardTerminalValue_le_liveBellmanValue
      reward roots who deviation
  have hgapBound : ∀ time,
      max (deviationValue time - prescribed time) 0 ≤ 2 * bound := by
    intro time
    have hdev := abs_quittingTerminalPayoff_le reward
      (quittingRootSequenceProfile reward
        (quittingRootSequenceUpdate roots who deviation) time)
      who hbound0 hreward
    have hpres := abs_quittingTerminalPayoff_le reward
      (quittingRootSequenceProfile reward roots time)
      who hbound0 hreward
    have hraw : deviationValue time - prescribed time ≤ 2 * bound := by
      dsimp [deviationValue, prescribed,
        quittingRootSequenceHazardTerminalValue,
        quittingRootSequenceTerminalValue]
      rw [abs_le] at hdev hpres
      linarith
    exact max_le hraw (by linarith)
  have hboundary : Tendsto (fun fuel =>
      quittingOpponentSurvivalWeight roots who 0 fuel *
        max (deviationValue fuel - prescribed fuel) 0) atTop (nhds 0) := by
    apply squeeze_zero
    · intro fuel
      exact mul_nonneg
        (quittingOpponentSurvivalWeight_nonneg roots who 0 fuel)
        (le_max_right _ _)
    · intro fuel
      exact mul_le_mul_of_nonneg_left (hgapBound fuel)
        (quittingOpponentSurvivalWeight_nonneg roots who 0 fuel)
    · simpa using hsurvival.mul_const (2 * bound)
  exact quittingSubBellmanGap_le_tsum_residual_of_boundary_tendsto_zero
    reward roots who prescribed deviationValue hdeviation hresidual
      hsummable hboundary

/-- Umbrella form of the local-to-global conclusion.  The same weighted
residual bound holds either when opponent survival contracts to zero, or—on
the only possible positive-survival branch—when the singleton reward is
nonnegative. -/
theorem quittingRootSequenceHazardTerminalGap_le_tsum_residual_of_zero_or_nonnegativeSolo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (deviation : ℕ → PMF Bool) (bound limit : ℝ)
    (hbound0 : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hlimit : Tendsto
      (quittingOpponentSurvivalWeight roots who 0) atTop (nhds limit))
    (hbranch : limit = 0 ∨
      0 ≤ reward (quittingSingletonTerminal who) who)
    (hsummable : Summable (fun time =>
      quittingOpponentSurvivalWeight roots who 0 time *
        quittingPrescribedOneStepResidual reward roots who
          (quittingRootSequenceTerminalValue reward roots who) time)) :
    quittingRootSequenceHazardTerminalValue reward roots who deviation 0 -
        quittingRootSequenceTerminalValue reward roots who 0 ≤
      ∑' time, quittingOpponentSurvivalWeight roots who 0 time *
        quittingPrescribedOneStepResidual reward roots who
          (quittingRootSequenceTerminalValue reward roots who) time := by
  rcases hbranch with hzero | hsolo
  · apply quittingRootSequenceHazardTerminalGap_le_tsum_residual_of_survival_zero
      reward roots who deviation bound hbound0 hreward
    · simpa only [hzero] using hlimit
    · exact hsummable
  · by_cases hzero : limit = 0
    · apply quittingRootSequenceHazardTerminalGap_le_tsum_residual_of_survival_zero
        reward roots who deviation bound hbound0 hreward
      · simpa only [hzero] using hlimit
      · exact hsummable
    · have hlimit0 : 0 ≤ limit := by
        apply ge_of_tendsto' hlimit
        exact quittingOpponentSurvivalWeight_nonneg roots who 0
      have hlimitPos : 0 < limit := lt_of_le_of_ne hlimit0 (Ne.symm hzero)
      exact quittingRootSequenceHazardTerminalGap_le_tsum_residual
        reward roots who deviation bound limit hbound0 (fun S => hreward S who)
          hsolo hlimit hlimitPos hsummable

end GameTheory
