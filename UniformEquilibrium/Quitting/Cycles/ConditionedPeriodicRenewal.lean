/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryConditioning
import UniformEquilibrium.Quitting.Cycles.PeriodicWindowEvaluation

/-!
# Long-window periodic renewal realizes conditioned tail payoffs

For a prescribed quitting tail converging to a phantom boundary, repeat the
finite window beginning at a fixed date.  The normalized payoff of one pass
converges to the tail annotation conditioned on eventual absorption.  This is
the exact renewal bridge

`(value start - survival * value endpoint) / (1 - survival)`

from analytic conditioned values to honest finite-window restart deliveries.
It does not assert that the resulting periodic profiles are near-minimal or
approximately Nash; those are separate strategic questions.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The nonempty root window `[start, start + window]`, read as one cycle. -/
def quittingTailWindowCycle
    (roots : ℕ → ι → PMF Bool) (start window : ℕ) :
    Fin (window + 1) → ι → PMF Bool :=
  fun phase ↦ roots (start + phase.val)

/-- The honest infinite root sequence obtained by periodically repeating the
nonempty tail window `[start, start + window]`. -/
def quittingPeriodizedTailWindowRoots
    (roots : ℕ → ι → PMF Bool) (start window : ℕ) :
    ℕ → ι → PMF Bool :=
  quittingCyclicRootSequence (quittingTailWindowCycle roots start window) 0

omit [Fintype ι] [DecidableEq ι] in
/-- During its first pass, a periodized tail window agrees with the source
tail at the corresponding date. -/
theorem quittingPeriodizedTailWindowRoots_of_lt
    (roots : ℕ → ι → PMF Bool) (start window time : ℕ)
    (htime : time < window + 1) :
    quittingPeriodizedTailWindowRoots roots start window time =
      roots (start + time) := by
  unfold quittingPeriodizedTailWindowRoots quittingCyclicRootSequence
    quittingTailWindowCycle quittingCyclicOrbit
  simp [Nat.mod_eq_of_lt htime]

omit [Fintype ι] [DecidableEq ι] in
/-- The periodized tail window has literal period `window + 1`. -/
theorem quittingPeriodizedTailWindowRoots_add_period
    (roots : ℕ → ι → PMF Bool) (start window time : ℕ) :
    quittingPeriodizedTailWindowRoots roots start window
        (time + (window + 1)) =
      quittingPeriodizedTailWindowRoots roots start window time := by
  exact quittingCyclicRootSequence_add_period
    (quittingTailWindowCycle roots start window) 0 time

omit [DecidableEq ι] in
/-- Every prefix contained in the first pass has the same joint survival as
the corresponding source-tail prefix. -/
theorem quittingJointSurvivalWeight_periodizedTailWindow
    (roots : ℕ → ι → PMF Bool) (start window fuel : ℕ)
    (hfuel : fuel ≤ window + 1) :
    quittingJointSurvivalWeight
        (quittingPeriodizedTailWindowRoots roots start window) 0 fuel =
      quittingJointSurvivalWeight roots start fuel := by
  calc
    quittingJointSurvivalWeight
          (quittingPeriodizedTailWindowRoots roots start window) 0 fuel =
        quittingJointSurvivalWeight (fun time ↦ roots (start + time)) 0 fuel := by
      apply quittingJointSurvivalWeight_congr _ _ 0 fuel
      intro offset hoffset
      simp only [Nat.zero_add]
      exact quittingPeriodizedTailWindowRoots_of_lt roots start window offset
        (lt_of_lt_of_le hoffset hfuel)
    _ = quittingJointSurvivalWeight roots start fuel :=
      (quittingJointSurvivalWeight_eq_shift roots start fuel).symm

omit [DecidableEq ι] in
/-- One pass of the periodized roots has exactly the source window's
normalized absorbing delivery. -/
theorem quittingWindowRestartDelivery_periodizedTailWindow
    (roots : ℕ → ι → PMF Bool) (start window : ℕ) (who : ι) :
    quittingWindowRestartDelivery reward
        (quittingPeriodizedTailWindowRoots roots start window) who 0
          (window + 1) =
      quittingWindowRestartDelivery reward roots who start (window + 1) := by
  unfold quittingWindowRestartDelivery quittingWindowAbsorbingIntercept
  rw [quittingJointSurvivalWeight_periodizedTailWindow
    roots start window (window + 1) le_rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro offset hoffset
  have hoffset_lt : offset < window + 1 := Finset.mem_range.mp hoffset
  rw [quittingJointSurvivalWeight_periodizedTailWindow
    roots start window offset (Nat.le_of_lt hoffset_lt)]
  simp only [Nat.zero_add]
  rw [quittingPeriodizedTailWindowRoots_of_lt
    roots start window offset hoffset_lt]

omit [DecidableEq ι] in
/-- A positive-absorption periodized tail window has actual terminal payoff
equal to the source window's normalized renewal delivery. -/
theorem quittingCyclicTerminalValue_tailWindow_eq_restartDelivery
    (roots : ℕ → ι → PMF Bool) (start window : ℕ) (who : ι)
    (hsurvival :
      quittingJointSurvivalWeight roots start (window + 1) < 1) :
    quittingCyclicTerminalValue reward
        (quittingTailWindowCycle roots start window) 0 who =
      quittingWindowRestartDelivery reward roots who start (window + 1) := by
  change quittingRootSequenceTerminalValue reward
      (quittingPeriodizedTailWindowRoots roots start window) who 0 = _
  rw [quittingRootSequenceTerminalValue_eq_windowRestartDelivery_of_periodic
    reward (quittingPeriodizedTailWindowRoots roots start window) who
      (window + 1)
      (quittingPeriodizedTailWindowRoots_add_period roots start window)]
  · exact quittingWindowRestartDelivery_periodizedTailWindow
      roots start window who
  · rwa [quittingJointSurvivalWeight_periodizedTailWindow
      roots start window (window + 1) le_rfl]

omit [DecidableEq ι] in
/-- **Conditioned renewal limit.**  At a tail date with positive eventual
absorption, the delivery obtained by normalizing longer and longer finite
windows converges coordinatewise to the phantom-free conditioned value. -/
theorem tendsto_quittingWindowRestartDelivery_conditionedValue
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hboundary : ∀ player,
      Tendsto (fun time ↦ value time player) atTop
        (nhds (boundary player)))
    (start : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots start)
    (who : ι) :
    Tendsto
      (fun fuel ↦ quittingWindowRestartDelivery reward roots who start fuel)
      atTop
      (nhds (quittingTailConditionedValue roots value boundary start who)) := by
  let prescribed : ℕ → ℝ := fun time ↦ value time who
  have hprescribed :
      IsQuittingLivePrescribedValue reward roots who prescribed := by
    intro time
    have hcoordinate := congrFun (hpolicy time) who
    rw [quittingRootSuccessorPayoff_apply_eq_affine] at hcoordinate
    rw [quittingRootSuccessorPayoff_apply_eq_affine]
    exact hcoordinate
  have hsurvival := tendsto_quittingJointSurvivalLimit roots start
  have hfar : Tendsto (fun fuel ↦ prescribed (start + fuel)) atTop
      (nhds (boundary who)) := by
    simpa [prescribed, Function.comp_def, Nat.add_comm] using
      (hboundary who).comp (tendsto_add_atTop_nat start)
  have hnumerator : Tendsto
      (fun fuel ↦ prescribed start -
        quittingJointSurvivalWeight roots start fuel *
          prescribed (start + fuel)) atTop
      (nhds (prescribed start -
        quittingJointSurvivalLimit roots start * boundary who)) :=
    tendsto_const_nhds.sub (hsurvival.mul hfar)
  have hdenominator : Tendsto
      (fun fuel ↦ 1 - quittingJointSurvivalWeight roots start fuel) atTop
      (nhds (1 - quittingJointSurvivalLimit roots start)) :=
    tendsto_const_nhds.sub hsurvival
  have hdenominator_ne :
      1 - quittingJointSurvivalLimit roots start ≠ 0 := by
    exact ne_of_gt hpositive
  have hquotient := hnumerator.div hdenominator hdenominator_ne
  apply hquotient.congr'
  filter_upwards [] with fuel
  have htelescope :=
    quittingPrescribedValue_eq_windowIntercept_add_survival_mul
      reward roots who prescribed hprescribed start fuel
  unfold quittingWindowRestartDelivery
  change (prescribed start -
        quittingJointSurvivalWeight roots start fuel *
          prescribed (start + fuel)) /
      (1 - quittingJointSurvivalWeight roots start fuel) =
    quittingWindowAbsorbingIntercept reward roots who start fuel /
      (1 - quittingJointSurvivalWeight roots start fuel)
  rw [show quittingWindowAbsorbingIntercept reward roots who start fuel =
      prescribed start -
        quittingJointSurvivalWeight roots start fuel *
          prescribed (start + fuel) by linarith]

omit [DecidableEq ι] in
/-- **Literal periodic renewal realization.**  The actual terminal payoffs of
the honest behavior profiles obtained by repeating longer tail windows
converge to the conditioned tail annotation. -/
theorem tendsto_quittingTerminalPayoff_periodizedTailWindow_conditionedValue
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hboundary : ∀ player,
      Tendsto (fun time ↦ value time player) atTop
        (nhds (boundary player)))
    (start : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots start)
    (who : ι) :
    Tendsto
      (fun window ↦
        quittingTerminalPayoff reward
          (quittingCyclicBehaviorProfile reward
            (quittingTailWindowCycle roots start window) 0) who)
      atTop
      (nhds (quittingTailConditionedValue roots value boundary start who)) := by
  have hrestart :=
    tendsto_quittingWindowRestartDelivery_conditionedValue
      roots value boundary hpolicy hboundary start hpositive who
  have hrestart_succ : Tendsto
      (fun window ↦
        quittingWindowRestartDelivery reward roots who start (window + 1))
      atTop
      (nhds (quittingTailConditionedValue roots value boundary start who)) := by
    simpa [Function.comp_def] using
      hrestart.comp (tendsto_add_atTop_nat 1)
  have hlimit_lt : quittingJointSurvivalLimit roots start < 1 := by
    unfold quittingTailEventualAbsorption at hpositive
    linarith
  have hsurvival_succ : Tendsto
      (fun window ↦ quittingJointSurvivalWeight roots start (window + 1))
      atTop (nhds (quittingJointSurvivalLimit roots start)) := by
    simpa [Function.comp_def] using
      (tendsto_quittingJointSurvivalLimit roots start).comp
        (tendsto_add_atTop_nat 1)
  have heventual : ∀ᶠ window : ℕ in atTop,
      quittingJointSurvivalWeight roots start (window + 1) < 1 :=
    hsurvival_succ.eventually (Iio_mem_nhds hlimit_lt)
  apply hrestart_succ.congr'
  filter_upwards [heventual] with window hsurvival
  rw [quittingTerminalPayoff_cyclicBehaviorProfile]
  exact (quittingCyclicTerminalValue_tailWindow_eq_restartDelivery
    roots start window who hsurvival).symm

end GameTheory
