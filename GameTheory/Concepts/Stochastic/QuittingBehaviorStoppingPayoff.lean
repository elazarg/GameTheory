/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingBehaviorStoppingLaw

/-!
# Payoff mixture over the live-spine stopping law

The finite pure-time decomposition of a quitting hazard has one atom for
each finite Quit date and one final atom for continuing through the cutoff.
Passing that identity to the terminal-payoff limit turns the final atom into
Never and the finite weights into the stopping-law atoms.

Thus every behavioral strategy payoff is exactly the expectation of its
deterministic Quit-time/Never payoffs under its induced stopping law.  This is
a one-player mixture statement against fixed opponents; it does not construct
a joint stopping-time process or add a filtration API.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem quittingFiniteRootPayoff_eq_stoppingMass_decomposition
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    quittingFiniteRootPayoff reward roots who hazard 0 cutoff =
      (∑ time ∈ Finset.range cutoff,
        quittingHazardStopMass hazard time *
          quittingRootSequencePureTimeTerminalValue reward roots who
            (some time) 0) +
        quittingHazardSurvival hazard cutoff *
          quittingFiniteRootPayoff reward roots who
            (quittingPureTimeHazard none) 0 cutoff := by
  rw [quittingFiniteRootPayoff_eq_sum_pureTime,
    Fin.sum_univ_castSucc,
    quittingFiniteHazardWeight_last,
    quittingFinitePureTimePayoff_last_eq_neverFinite]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro choice _
    rw [quittingFiniteHazardWeight_castSucc,
      quittingFinitePureTimePayoff_castSucc_eq_terminal]
    simp only [Nat.zero_add]
    rfl
  · simp [quittingHazardSurvival]

/-- An arbitrary live-spine hazard payoff is the stopping-law expectation of
its deterministic finite-Quit and Never payoffs. -/
theorem quittingRootSequenceHazardTerminalValue_eq_expect_stoppingLaw
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    quittingRootSequenceHazardTerminalValue reward roots who hazard 0 =
      expect (quittingHazardStoppingLaw hazard)
        (fun choice =>
          quittingRootSequencePureTimeTerminalValue reward roots who
            choice 0) := by
  let pureValue : Option ℕ → ℝ := fun choice =>
    quittingRootSequencePureTimeTerminalValue reward roots who choice 0
  have hpureBound : ∀ choice, |pureValue choice| ≤ M := by
    intro choice
    simpa [pureValue, quittingRootSequencePureTimeTerminalValue,
      quittingRootSequenceHazardTerminalValue,
      quittingRootSequenceTerminalValue] using
      (abs_quittingTerminalPayoff_le reward
        (quittingRootSequenceProfile reward
          (quittingRootSequenceUpdate roots who
            (quittingPureTimeHazard choice)) 0)
        who hM hreward)
  have hsource : Tendsto
      (fun cutoff =>
        quittingFiniteRootPayoff reward roots who hazard 0 cutoff)
      atTop (nhds
        (quittingRootSequenceHazardTerminalValue reward roots who hazard 0)) := by
    simpa [quittingRootSequenceHazardTerminalValue,
      quittingRootSequenceTerminalValue] using
      (tendsto_quittingFiniteRootPayoff_terminal
        reward roots who hazard 0)
  have hnever : Tendsto
      (fun cutoff =>
        quittingFiniteRootPayoff reward roots who
          (quittingPureTimeHazard none) 0 cutoff)
      atTop (nhds (pureValue none)) := by
    simpa [pureValue, quittingRootSequencePureTimeTerminalValue,
      quittingRootSequenceHazardTerminalValue,
      quittingRootSequenceTerminalValue] using
      (tendsto_quittingFiniteRootPayoff_terminal reward roots who
        (quittingPureTimeHazard none) 0)
  have hfiniteSummable : Summable (fun time =>
      quittingHazardStopMass hazard time * pureValue (some time)) := by
    have hmajor : Summable (fun time =>
        M * quittingHazardStopMass hazard time) :=
      (hasSum_quittingHazardStopMass hazard).summable.mul_left M
    apply Summable.of_norm_bounded hmajor
    intro time
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (quittingHazardStopMass_nonneg hazard time)]
    calc
      quittingHazardStopMass hazard time * |pureValue (some time)| ≤
          quittingHazardStopMass hazard time * M := by
        exact mul_le_mul_of_nonneg_left (hpureBound (some time))
          (quittingHazardStopMass_nonneg hazard time)
      _ = M * quittingHazardStopMass hazard time := by ring
  have hfinite : Tendsto
      (fun cutoff => ∑ time ∈ Finset.range cutoff,
        quittingHazardStopMass hazard time * pureValue (some time))
      atTop (nhds (∑' time : ℕ,
        quittingHazardStopMass hazard time * pureValue (some time))) :=
    hfiniteSummable.hasSum.tendsto_sum_nat
  have hlast : Tendsto
      (fun cutoff =>
        quittingHazardSurvival hazard cutoff *
          quittingFiniteRootPayoff reward roots who
            (quittingPureTimeHazard none) 0 cutoff)
      atTop (nhds
        (quittingHazardNeverMass hazard * pureValue none)) :=
    (tendsto_quittingHazardSurvival_neverMass hazard).mul hnever
  have hdecomposition : Tendsto
      (fun cutoff =>
        quittingFiniteRootPayoff reward roots who hazard 0 cutoff)
      atTop (nhds
        ((∑' time : ℕ,
          quittingHazardStopMass hazard time * pureValue (some time)) +
            quittingHazardNeverMass hazard * pureValue none)) := by
    rw [show (fun cutoff =>
        quittingFiniteRootPayoff reward roots who hazard 0 cutoff) =
      fun cutoff =>
        (∑ time ∈ Finset.range cutoff,
          quittingHazardStopMass hazard time * pureValue (some time)) +
          quittingHazardSurvival hazard cutoff *
            quittingFiniteRootPayoff reward roots who
              (quittingPureTimeHazard none) 0 cutoff by
      funext cutoff
      exact quittingFiniteRootPayoff_eq_stoppingMass_decomposition
        reward roots who hazard cutoff]
    exact hfinite.add hlast
  have hvalue := tendsto_nhds_unique hsource hdecomposition
  rw [quittingHazardStoppingLaw_expect hazard pureValue hpureBound]
  dsimp only [pureValue]
  linarith

/-- Behavioral form: a unilateral strategy payoff is the stopping-law
mixture of its pure live-spine Quit-time/Never deviations. -/
theorem quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (strategy : (quittingGame reward).BehaviorStrategy who)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    quittingTerminalPayoff reward
        (Function.update profile who strategy) who =
      expect (quittingBehaviorStoppingLaw reward strategy)
        (fun choice =>
          quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who choice)) who) := by
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingRootSequenceHazardTerminalValue_eq_expect_stoppingLaw
      reward (quittingProfileLiveRoot reward profile) who
        (quittingBehaviorLiveHazard reward strategy) hM hreward]
  apply congrArg
  funext choice
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]

end GameTheory
