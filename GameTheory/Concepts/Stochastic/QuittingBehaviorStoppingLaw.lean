/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingBehaviorPureTimeExtremality
import Math.Probability.DiscreteHazardStopping

/-! # Stopping law of a live-spine quitting behavior

The generic construction lives in `Math.Probability.DiscreteHazard`; this
file is the backwards-compatible quitting-game spelling of that API. -/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction
open Math.Probability.DiscreteHazard

def quittingHazardSurvival (hazard : ℕ → PMF Bool) (cutoff : ℕ) : ℝ :=
  Math.survivalProduct (fun time => (hazard time false).toReal) 0 cutoff

/-- The quitting-game survival spelling agrees with the usual finite product
of per-stage continuation probabilities. -/
theorem quittingHazardSurvival_eq_prod (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    quittingHazardSurvival hazard cutoff =
      ∏ time ∈ Finset.range cutoff, (hazard time false).toReal := by
  simp [quittingHazardSurvival, Math.survivalProduct]

@[simp] theorem quittingHazardSurvival_zero (hazard : ℕ → PMF Bool) :
    quittingHazardSurvival hazard 0 = 1 := by simp [quittingHazardSurvival]

theorem quittingHazard_continue_add_quit (hazard : ℕ → PMF Bool) (time : ℕ) :
    (hazard time false).toReal + (hazard time true).toReal = 1 :=
  continue_add_stop hazard time

theorem quittingHazard_continue_nonneg (hazard : ℕ → PMF Bool) (time : ℕ) :
    0 ≤ (hazard time false).toReal := continue_nonneg hazard time

theorem quittingHazard_quit_nonneg (hazard : ℕ → PMF Bool) (time : ℕ) :
    0 ≤ (hazard time true).toReal := stop_nonneg hazard time

theorem quittingHazard_continue_le_one (hazard : ℕ → PMF Bool) (time : ℕ) :
    (hazard time false).toReal ≤ 1 := continue_le_one hazard time

theorem quittingHazardSurvival_nonneg (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    0 ≤ quittingHazardSurvival hazard cutoff :=
  Math.survivalProduct_nonneg _ (quittingHazard_continue_nonneg hazard) _ _

theorem quittingHazardSurvival_le_one (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    quittingHazardSurvival hazard cutoff ≤ 1 :=
  Math.survivalProduct_le_one _ (quittingHazard_continue_nonneg hazard)
    (quittingHazard_continue_le_one hazard) _ _

theorem quittingHazardSurvival_succ (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    quittingHazardSurvival hazard (cutoff + 1) =
      quittingHazardSurvival hazard cutoff * (hazard cutoff false).toReal := by
  simpa [quittingHazardSurvival] using
    Math.survivalProduct_succ (fun time => (hazard time false).toReal) 0 cutoff

theorem antitone_quittingHazardSurvival (hazard : ℕ → PMF Bool) :
    Antitone (quittingHazardSurvival hazard) := by
  apply antitone_nat_of_succ_le
  intro cutoff
  rw [quittingHazardSurvival_succ]
  exact mul_le_of_le_one_right (quittingHazardSurvival_nonneg hazard cutoff)
    (quittingHazard_continue_le_one hazard cutoff)

private theorem scalar_survival_eq (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    (BooleanHazard.toScalar hazard).survival 0 cutoff = quittingHazardSurvival hazard cutoff := by
  rw [← BooleanHazard.survival_eq_scalar]
  rfl

/-- Compatibility aliases for the generic scalarized Boolean hazard. -/
def quittingHazardNeverMass (hazard : ℕ → PMF Bool) : ℝ := (BooleanHazard.toScalar hazard).neverMass
def quittingHazardStopMass (hazard : ℕ → PMF Bool) (time : ℕ) : ℝ :=
  (BooleanHazard.toScalar hazard).stopMass time
def quittingHazardStoppingLaw (hazard : ℕ → PMF Bool) : PMF (Option ℕ) :=
  (BooleanHazard.toScalar hazard).stoppingLaw

/-- The compatibility stop mass is finite survival through `time`, followed
by stopping at `time`. -/
theorem quittingHazardStopMass_eq_survival_mul_stop
    (hazard : ℕ → PMF Bool) (time : ℕ) :
    quittingHazardStopMass hazard time =
      quittingHazardSurvival hazard time * (hazard time true).toReal := by
  unfold quittingHazardStopMass ScalarHazard.stopMass
  rw [scalar_survival_eq]
  rfl

theorem quittingHazardNeverMass_nonneg (hazard : ℕ → PMF Bool) :
    0 ≤ quittingHazardNeverMass hazard := ScalarHazard.neverMass_nonneg _

theorem quittingHazardNeverMass_le_survival (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    quittingHazardNeverMass hazard ≤ quittingHazardSurvival hazard cutoff := by
  rw [← scalar_survival_eq]
  exact ScalarHazard.neverMass_le_survival _ _

theorem tendsto_quittingHazardSurvival_neverMass (hazard : ℕ → PMF Bool) :
    Tendsto (quittingHazardSurvival hazard) atTop (nhds (quittingHazardNeverMass hazard)) := by
  have hs : quittingHazardSurvival hazard = (BooleanHazard.toScalar hazard).survival 0 := by
    funext n
    exact (scalar_survival_eq hazard n).symm
  rw [hs]
  exact ScalarHazard.tendsto_survival_neverMass _

theorem quittingHazardStopMass_nonneg (hazard : ℕ → PMF Bool) (time : ℕ) :
    0 ≤ quittingHazardStopMass hazard time := ScalarHazard.stopMass_nonneg _ _

theorem quittingHazardStopMass_eq_survival_sub_succ (hazard : ℕ → PMF Bool) (time : ℕ) :
    quittingHazardStopMass hazard time = quittingHazardSurvival hazard time -
      quittingHazardSurvival hazard (time + 1) := by
  rw [← scalar_survival_eq, ← scalar_survival_eq]
  exact ScalarHazard.stopMass_eq_survival_sub_succ _ _

theorem sum_quittingHazardStopMass (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff, quittingHazardStopMass hazard time) =
      1 - quittingHazardSurvival hazard cutoff := by
  rw [← scalar_survival_eq]
  exact ScalarHazard.sum_stopMass _ _

theorem hasSum_quittingHazardStopMass (hazard : ℕ → PMF Bool) :
    HasSum (quittingHazardStopMass hazard) (1 - quittingHazardNeverMass hazard) :=
  ScalarHazard.hasSum_stopMass _

theorem tendsto_quittingHazardStopMass_zero (hazard : ℕ → PMF Bool) :
    Tendsto (quittingHazardStopMass hazard) atTop (nhds 0) :=
  (hasSum_quittingHazardStopMass hazard).summable.tendsto_atTop_zero

@[simp] theorem quittingHazardStoppingLaw_none_toReal (hazard : ℕ → PMF Bool) :
    (quittingHazardStoppingLaw hazard none).toReal = quittingHazardNeverMass hazard :=
  ScalarHazard.stoppingLaw_none_toReal _

@[simp] theorem quittingHazardStoppingLaw_some_toReal (hazard : ℕ → PMF Bool) (time : ℕ) :
    (quittingHazardStoppingLaw hazard (some time)).toReal = quittingHazardStopMass hazard time :=
  ScalarHazard.stoppingLaw_some_toReal _ _

theorem quittingHazardStoppingLaw_toReal_tsum_one (hazard : ℕ → PMF Bool) :
    ∑' choice : Option ℕ, (quittingHazardStoppingLaw hazard choice).toReal = 1 :=
  pmf_toReal_tsum_one _

theorem quittingHazardStoppingLaw_expect (hazard : ℕ → PMF Bool) (value : Option ℕ → ℝ)
    {M : ℝ} (hvalue : ∀ choice, |value choice| ≤ M) :
    expect (quittingHazardStoppingLaw hazard) value =
      quittingHazardNeverMass hazard * value none +
        ∑' time : ℕ, quittingHazardStopMass hazard time * value (some time) :=
  ScalarHazard.stoppingLaw_expect _ value hvalue

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def quittingBehaviorStoppingLaw
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {who : ι} (strategy : (quittingGame reward).BehaviorStrategy who) : PMF (Option ℕ) :=
  quittingHazardStoppingLaw (quittingBehaviorLiveHazard reward strategy)

omit [DecidableEq ι] in
@[simp] theorem quittingBehaviorStoppingLaw_none_toReal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {who : ι} (strategy : (quittingGame reward).BehaviorStrategy who) :
    (quittingBehaviorStoppingLaw reward strategy none).toReal =
      quittingHazardNeverMass (quittingBehaviorLiveHazard reward strategy) := by
  simp [quittingBehaviorStoppingLaw]

omit [DecidableEq ι] in
@[simp] theorem quittingBehaviorStoppingLaw_some_toReal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {who : ι} (strategy : (quittingGame reward).BehaviorStrategy who) (time : ℕ) :
    (quittingBehaviorStoppingLaw reward strategy (some time)).toReal =
      quittingHazardStopMass (quittingBehaviorLiveHazard reward strategy) time := by
  simp [quittingBehaviorStoppingLaw]

end GameTheory
