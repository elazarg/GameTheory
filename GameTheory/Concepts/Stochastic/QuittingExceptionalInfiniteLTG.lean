/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingExceptionalTailLimits

/-!
# Infinite local-to-global bound for the exceptional quitting clock

This file closes the positive-survival branch directly for each unilateral
hazard sequence.  The finite exceptional `π`/`α` estimate controls the
surviving positive payoff gap at late live cutoffs.  A sub-Bellman telescope
then sends that boundary term to zero and charges the deviation only to the
summable weighted prescribed residuals.
-/

set_option autoImplicit false

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

end GameTheory
