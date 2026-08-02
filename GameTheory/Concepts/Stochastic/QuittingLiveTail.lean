/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingLiveMassRecurrence

/-!
# Live tails and terminal-payoff error in quitting games

The live mass decreases to a limit.  Conservation of probability identifies
the mass absorbed after any cutoff with current live mass minus its limit.
Consequently, terminal payoff differs from the payoff of the cutoff state by
at most the reward bound times that live tail.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Limiting probability that play never leaves the live state. -/
def quittingLiveMassLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) : ℝ :=
  ⨅ time, quittingLiveMass reward profile time

omit [DecidableEq ι] in
/-- Live mass converges monotonically to its infimum. -/
theorem tendsto_quittingLiveMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    Tendsto (quittingLiveMass reward profile) atTop
      (nhds (quittingLiveMassLimit reward profile)) := by
  classical
  unfold quittingLiveMassLimit
  apply tendsto_atTop_ciInf (quittingLiveMass_antitone reward profile)
  refine ⟨0, ?_⟩
  rintro _ ⟨time, rfl⟩
  exact quittingLiveMass_nonneg reward profile time

omit [DecidableEq ι] in
/-- The limiting live mass is nonnegative. -/
theorem quittingLiveMassLimit_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    0 ≤ quittingLiveMassLimit reward profile := by
  unfold quittingLiveMassLimit
  exact le_ciInf fun time =>
    quittingLiveMass_nonneg reward profile time

omit [DecidableEq ι] in
/-- The limiting live mass is below every finite-time live mass. -/
theorem quittingLiveMassLimit_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingLiveMassLimit reward profile ≤
      quittingLiveMass reward profile time := by
  unfold quittingLiveMassLimit
  apply ciInf_le
  refine ⟨0, ?_⟩
  rintro _ ⟨stage, rfl⟩
  exact quittingLiveMass_nonneg reward profile stage

omit [DecidableEq ι] in
/-- At every time, live mass plus all absorbed-state masses is one. -/
theorem quittingLiveMass_add_sum_absorbedMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingLiveMass reward profile time +
      ∑ S, quittingAbsorbedMass reward profile time S = 1 := by
  classical
  letI : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  letI : ∀ who : ι, Finite ((quittingGame reward).Act who) :=
    fun _ => inferInstanceAs (Finite Bool)
  rw [quittingLiveMass_eq_expectedStateValue]
  unfold quittingAbsorbedMass StochasticGame.expectedStateValue
  rw [expect_sum_comm, ← expect_add]
  calc
    expect ((quittingGame reward).histDist profile none time)
        (fun history => quittingLiveIndicator reward history.2 +
          ∑ S, quittingAbsorbedIndicator reward S history.2) =
      expect ((quittingGame reward).histDist profile none time)
        (fun _ => (1 : ℝ)) := by
          apply congrArg
            (expect ((quittingGame reward).histDist profile none time))
          funext history
          cases history.2 with
          | none =>
              simp [quittingLiveIndicator, quittingAbsorbedIndicator,
                quittingGame]
          | some S =>
              simp [quittingLiveIndicator, quittingAbsorbedIndicator,
                quittingGame]
    _ = 1 := expect_const _ _

omit [DecidableEq ι] in
/-- Conservation of probability persists at the limit. -/
theorem quittingLiveMassLimit_add_sum_absorbedMassLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingLiveMassLimit reward profile +
      ∑ S, quittingAbsorbedMassLimit reward profile S = 1 := by
  classical
  have hlimit : Tendsto (fun time =>
      quittingLiveMass reward profile time +
        ∑ S, quittingAbsorbedMass reward profile time S) atTop
      (nhds (quittingLiveMassLimit reward profile +
        ∑ S, quittingAbsorbedMassLimit reward profile S)) :=
    (tendsto_quittingLiveMass reward profile).add
      (tendsto_finsetSum Finset.univ fun S _ =>
        tendsto_quittingAbsorbedMass reward profile S)
  have hconstant : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop
      (nhds (quittingLiveMassLimit reward profile +
        ∑ S, quittingAbsorbedMassLimit reward profile S)) := by
    simpa only [quittingLiveMass_add_sum_absorbedMass] using hlimit
  exact tendsto_nhds_unique hconstant tendsto_const_nhds

omit [DecidableEq ι] in
/-- Total probability of absorption strictly after the cutoff is current
live mass minus the probability of never absorbing. -/
theorem sum_absorbedMassLimit_sub_eq_liveTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    (∑ S, (quittingAbsorbedMassLimit reward profile S -
      quittingAbsorbedMass reward profile time S)) =
      quittingLiveMass reward profile time -
        quittingLiveMassLimit reward profile := by
  classical
  have hfinite :=
    quittingLiveMass_add_sum_absorbedMass reward profile time
  have hlimit :=
    quittingLiveMassLimit_add_sum_absorbedMassLimit reward profile
  rw [Finset.sum_sub_distrib]
  linarith

omit [DecidableEq ι] in
/-- Every finite-time absorbed mass is below its limiting mass. -/
theorem quittingAbsorbedMass_le_limit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (S : {S : Finset ι // S.Nonempty}) :
    quittingAbsorbedMass reward profile time S ≤
      quittingAbsorbedMassLimit reward profile S := by
  apply ge_of_tendsto (tendsto_quittingAbsorbedMass reward profile S)
  filter_upwards [Filter.eventually_ge_atTop time] with later hlater
  exact quittingAbsorbedMass_monotone reward profile S hlater

omit [DecidableEq ι] in
/-- Terminal payoff minus the payoff of the state reached at the cutoff is
the reward-weighted future absorption mass. -/
theorem quittingTerminalPayoff_sub_expectedStagePayoff_eq_sum_liveTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (time : ℕ) (who : ι) :
    quittingTerminalPayoff reward profile who -
        (quittingGame reward).expectedStagePayoff profile none time who =
      ∑ S, (quittingAbsorbedMassLimit reward profile S -
        quittingAbsorbedMass reward profile time S) * reward S who := by
  rw [quittingTerminalPayoff,
    expectedStagePayoff_quittingGame_eq_sum_mass,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  ring

omit [DecidableEq ι] in
/-- Quantitative terminal-tail estimate. -/
theorem abs_quittingTerminalPayoff_sub_expectedStagePayoff_le_liveTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (time : ℕ) (who : ι) (bound : ℝ)
    (hreward : ∀ S, |reward S who| ≤ bound) :
    |quittingTerminalPayoff reward profile who -
        (quittingGame reward).expectedStagePayoff profile none time who| ≤
      bound * (quittingLiveMass reward profile time -
        quittingLiveMassLimit reward profile) := by
  classical
  rw [quittingTerminalPayoff_sub_expectedStagePayoff_eq_sum_liveTail]
  calc
    |∑ S, (quittingAbsorbedMassLimit reward profile S -
        quittingAbsorbedMass reward profile time S) * reward S who| ≤
      ∑ S, |(quittingAbsorbedMassLimit reward profile S -
        quittingAbsorbedMass reward profile time S) * reward S who| := by
          simpa using Finset.abs_sum_le_sum_abs
            (fun S : {S : Finset ι // S.Nonempty} =>
              (quittingAbsorbedMassLimit reward profile S -
                quittingAbsorbedMass reward profile time S) * reward S who)
            Finset.univ
    _ = ∑ S, (quittingAbsorbedMassLimit reward profile S -
          quittingAbsorbedMass reward profile time S) * |reward S who| := by
      apply Finset.sum_congr rfl
      intro S _
      rw [abs_mul, abs_of_nonneg]
      linarith [quittingAbsorbedMass_le_limit
        reward profile time S]
    _ ≤ ∑ S, (quittingAbsorbedMassLimit reward profile S -
          quittingAbsorbedMass reward profile time S) * bound := by
      apply Finset.sum_le_sum
      intro S _
      exact mul_le_mul_of_nonneg_left (hreward S)
        (sub_nonneg.mpr
          (quittingAbsorbedMass_le_limit reward profile time S))
    _ = bound * (quittingLiveMass reward profile time -
          quittingLiveMassLimit reward profile) := by
      rw [← Finset.sum_mul,
        sum_absorbedMassLimit_sub_eq_liveTail]
      ring

end GameTheory
