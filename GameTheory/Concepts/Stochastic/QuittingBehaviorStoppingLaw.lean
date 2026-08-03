/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingBehaviorPureTimeExtremality

/-!
# Stopping law of a live-spine quitting behavior

Before absorption, a quitting game has a unique public live history.  A
behavior strategy therefore supplies a Boolean hazard at every live date.
This file packages those hazards as a probability mass function on
`Option ℕ`: `some t` means first Quit at date `t`, while `none` means Never.

The construction retains the exact finite first-Quit atoms and defines the
Never atom as the limit of the antitone finite survival products.  These
atoms sum to one.  No stopping-time filtration, payoff representation, or
best-response theorem is introduced here.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction

/-- Probability of continuing through the first `cutoff` live dates under a
Boolean hazard sequence. -/
def quittingHazardSurvival
    (hazard : ℕ → PMF Bool) (cutoff : ℕ) : ℝ :=
  ∏ time ∈ Finset.range cutoff, (hazard time false).toReal

@[simp] theorem quittingHazardSurvival_zero
    (hazard : ℕ → PMF Bool) :
    quittingHazardSurvival hazard 0 = 1 := by
  simp [quittingHazardSurvival]

theorem quittingHazard_continue_add_quit
    (hazard : ℕ → PMF Bool) (time : ℕ) :
    (hazard time false).toReal + (hazard time true).toReal = 1 := by
  simpa [Fintype.sum_bool, add_comm] using
    pmf_toReal_sum_one (hazard time)

theorem quittingHazard_continue_nonneg
    (hazard : ℕ → PMF Bool) (time : ℕ) :
    0 ≤ (hazard time false).toReal :=
  ENNReal.toReal_nonneg

theorem quittingHazard_quit_nonneg
    (hazard : ℕ → PMF Bool) (time : ℕ) :
    0 ≤ (hazard time true).toReal :=
  ENNReal.toReal_nonneg

theorem quittingHazard_continue_le_one
    (hazard : ℕ → PMF Bool) (time : ℕ) :
    (hazard time false).toReal ≤ 1 := by
  linarith [quittingHazard_continue_add_quit hazard time,
    quittingHazard_quit_nonneg hazard time]

theorem quittingHazardSurvival_nonneg
    (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    0 ≤ quittingHazardSurvival hazard cutoff := by
  apply Finset.prod_nonneg
  intro time _
  exact quittingHazard_continue_nonneg hazard time

theorem quittingHazardSurvival_le_one
    (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    quittingHazardSurvival hazard cutoff ≤ 1 := by
  apply Finset.prod_le_one
  · intro time _
    exact quittingHazard_continue_nonneg hazard time
  · intro time _
    exact quittingHazard_continue_le_one hazard time

theorem quittingHazardSurvival_succ
    (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    quittingHazardSurvival hazard (cutoff + 1) =
      quittingHazardSurvival hazard cutoff *
        (hazard cutoff false).toReal := by
  simp [quittingHazardSurvival, Finset.prod_range_succ]

theorem antitone_quittingHazardSurvival
    (hazard : ℕ → PMF Bool) :
    Antitone (quittingHazardSurvival hazard) := by
  apply antitone_nat_of_succ_le
  intro cutoff
  rw [quittingHazardSurvival_succ]
  exact mul_le_of_le_one_right
    (quittingHazardSurvival_nonneg hazard cutoff)
    (quittingHazard_continue_le_one hazard cutoff)

/-- Probability of Never quitting, defined as the infimum of finite survival
probabilities. -/
def quittingHazardNeverMass (hazard : ℕ → PMF Bool) : ℝ :=
  ⨅ cutoff : ℕ, quittingHazardSurvival hazard cutoff

private theorem quittingHazardSurvival_bddBelow
    (hazard : ℕ → PMF Bool) :
    BddBelow (Set.range (quittingHazardSurvival hazard)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨cutoff, rfl⟩
  exact quittingHazardSurvival_nonneg hazard cutoff

theorem quittingHazardNeverMass_nonneg
    (hazard : ℕ → PMF Bool) :
    0 ≤ quittingHazardNeverMass hazard := by
  exact le_ciInf fun cutoff =>
    quittingHazardSurvival_nonneg hazard cutoff

theorem quittingHazardNeverMass_le_survival
    (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    quittingHazardNeverMass hazard ≤
      quittingHazardSurvival hazard cutoff := by
  exact ciInf_le (quittingHazardSurvival_bddBelow hazard) cutoff

theorem tendsto_quittingHazardSurvival_neverMass
    (hazard : ℕ → PMF Bool) :
    Tendsto (quittingHazardSurvival hazard) atTop
      (nhds (quittingHazardNeverMass hazard)) := by
  apply tendsto_atTop_ciInf (antitone_quittingHazardSurvival hazard)
  exact quittingHazardSurvival_bddBelow hazard

/-- Probability of first quitting at `time`. -/
def quittingHazardStopMass
    (hazard : ℕ → PMF Bool) (time : ℕ) : ℝ :=
  quittingHazardSurvival hazard time * (hazard time true).toReal

theorem quittingHazardStopMass_nonneg
    (hazard : ℕ → PMF Bool) (time : ℕ) :
    0 ≤ quittingHazardStopMass hazard time :=
  mul_nonneg (quittingHazardSurvival_nonneg hazard time)
    (quittingHazard_quit_nonneg hazard time)

theorem quittingHazardStopMass_eq_survival_sub_succ
    (hazard : ℕ → PMF Bool) (time : ℕ) :
    quittingHazardStopMass hazard time =
      quittingHazardSurvival hazard time -
        quittingHazardSurvival hazard (time + 1) := by
  rw [quittingHazardStopMass, quittingHazardSurvival_succ]
  have hsum := quittingHazard_continue_add_quit hazard time
  have hquit : (hazard time true).toReal =
      1 - (hazard time false).toReal := by
    linarith
  rw [hquit]
  ring

theorem sum_quittingHazardStopMass
    (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff,
      quittingHazardStopMass hazard time) =
        1 - quittingHazardSurvival hazard cutoff := by
  induction cutoff with
  | zero => simp
  | succ cutoff ih =>
      rw [Finset.sum_range_succ, ih,
        quittingHazardStopMass_eq_survival_sub_succ]
      ring

theorem hasSum_quittingHazardStopMass
    (hazard : ℕ → PMF Bool) :
    HasSum (quittingHazardStopMass hazard)
      (1 - quittingHazardNeverMass hazard) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (quittingHazardStopMass_nonneg hazard)
      (1 - quittingHazardNeverMass hazard)).2
  simpa only [sum_quittingHazardStopMass] using
    tendsto_const_nhds.sub
      (tendsto_quittingHazardSurvival_neverMass hazard)

theorem tendsto_quittingHazardStopMass_zero
    (hazard : ℕ → PMF Bool) :
    Tendsto (quittingHazardStopMass hazard) atTop (nhds 0) :=
  (hasSum_quittingHazardStopMass hazard).summable.tendsto_atTop_zero

private def quittingStoppingChoiceEquivNat : Option ℕ ≃ ℕ where
  toFun
    | none => 0
    | some time => time + 1
  invFun
    | 0 => none
    | time + 1 => some time
  left_inv choice := by cases choice <;> simp
  right_inv code := by cases code <;> simp

private def quittingHazardEncodedMass
    (hazard : ℕ → PMF Bool) : ℕ → ℝ
  | 0 => quittingHazardNeverMass hazard
  | time + 1 => quittingHazardStopMass hazard time

private theorem quittingHazardEncodedMass_nonneg
    (hazard : ℕ → PMF Bool) :
    ∀ code, 0 ≤ quittingHazardEncodedMass hazard code
  | 0 => quittingHazardNeverMass_nonneg hazard
  | time + 1 => quittingHazardStopMass_nonneg hazard time

private theorem sum_quittingHazardEncodedMass_succ
    (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    (∑ code ∈ Finset.range (cutoff + 1),
      quittingHazardEncodedMass hazard code) =
        quittingHazardNeverMass hazard +
          ∑ time ∈ Finset.range cutoff,
            quittingHazardStopMass hazard time := by
  induction cutoff with
  | zero => simp [quittingHazardEncodedMass]
  | succ cutoff ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [quittingHazardEncodedMass]
      ring

private theorem hasSum_quittingHazardEncodedMass
    (hazard : ℕ → PMF Bool) :
    HasSum (quittingHazardEncodedMass hazard) 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (quittingHazardEncodedMass_nonneg hazard) 1).2
  apply (tendsto_add_atTop_iff_nat 1).1
  have hstop := (hasSum_quittingHazardStopMass hazard).tendsto_sum_nat
  have hnever : Tendsto
      (fun _ : ℕ => quittingHazardNeverMass hazard) atTop
      (nhds (quittingHazardNeverMass hazard)) :=
    tendsto_const_nhds
  have hcombined := hnever.add hstop
  have hlimit : quittingHazardNeverMass hazard +
      (1 - quittingHazardNeverMass hazard) = 1 := by ring
  rw [hlimit] at hcombined
  simpa only [sum_quittingHazardEncodedMass_succ] using hcombined

private def quittingHazardEncodedLaw
    (hazard : ℕ → PMF Bool) : PMF ℕ :=
  ⟨fun code => ENNReal.ofReal (quittingHazardEncodedMass hazard code), by
    apply ENNReal.summable.hasSum_iff.2
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (quittingHazardEncodedMass_nonneg hazard)
      (hasSum_quittingHazardEncodedMass hazard).summable]
    rw [(hasSum_quittingHazardEncodedMass hazard).tsum_eq]
    norm_num⟩

/-- The stopping law induced by a Boolean live-spine hazard. -/
def quittingHazardStoppingLaw
    (hazard : ℕ → PMF Bool) : PMF (Option ℕ) :=
  (quittingHazardEncodedLaw hazard).map
    quittingStoppingChoiceEquivNat.symm

@[simp] theorem quittingHazardStoppingLaw_none_toReal
    (hazard : ℕ → PMF Bool) :
    (quittingHazardStoppingLaw hazard none).toReal =
      quittingHazardNeverMass hazard := by
  rw [quittingHazardStoppingLaw, map_equiv_apply]
  change (ENNReal.ofReal (quittingHazardNeverMass hazard)).toReal = _
  exact ENNReal.toReal_ofReal
    (quittingHazardNeverMass_nonneg hazard)

@[simp] theorem quittingHazardStoppingLaw_some_toReal
    (hazard : ℕ → PMF Bool) (time : ℕ) :
    (quittingHazardStoppingLaw hazard (some time)).toReal =
      quittingHazardStopMass hazard time := by
  rw [quittingHazardStoppingLaw, map_equiv_apply]
  change (ENNReal.ofReal (quittingHazardStopMass hazard time)).toReal = _
  exact ENNReal.toReal_ofReal
    (quittingHazardStopMass_nonneg hazard time)

/-- The real-valued finite atoms and Never atom of the stopping law sum to
one. -/
theorem quittingHazardStoppingLaw_toReal_tsum_one
    (hazard : ℕ → PMF Bool) :
    ∑' choice : Option ℕ,
      (quittingHazardStoppingLaw hazard choice).toReal = 1 :=
  pmf_toReal_tsum_one (quittingHazardStoppingLaw hazard)

/-- Expectation under the stopping law splits into its Never atom and its
finite first-Quit atoms.  Boundedness justifies the countable real sums. -/
theorem quittingHazardStoppingLaw_expect
    (hazard : ℕ → PMF Bool) (value : Option ℕ → ℝ)
    {M : ℝ} (hvalue : ∀ choice, |value choice| ≤ M) :
    expect (quittingHazardStoppingLaw hazard) value =
      quittingHazardNeverMass hazard * value none +
        ∑' time : ℕ,
          quittingHazardStopMass hazard time * value (some time) := by
  rw [quittingHazardStoppingLaw, expect_map]
  have hsummable := expect_summable_of_bounded
    (quittingHazardEncodedLaw hazard)
    (fun code => value (quittingStoppingChoiceEquivNat.symm code))
    (fun code => hvalue (quittingStoppingChoiceEquivNat.symm code))
  unfold expect
  rw [hsummable.tsum_eq_zero_add]
  congr 1
  · change (ENNReal.ofReal (quittingHazardNeverMass hazard)).toReal *
      value none = _
    rw [ENNReal.toReal_ofReal
      (quittingHazardNeverMass_nonneg hazard)]
  · apply tsum_congr
    intro time
    change (ENNReal.ofReal (quittingHazardStopMass hazard time)).toReal *
      value (some time) = _
    rw [ENNReal.toReal_ofReal
      (quittingHazardStopMass_nonneg hazard time)]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Stopping law read from a behavior strategy along the unique live public
history. -/
def quittingBehaviorStoppingLaw
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {who : ι} (strategy : (quittingGame reward).BehaviorStrategy who) :
    PMF (Option ℕ) :=
  quittingHazardStoppingLaw
    (quittingBehaviorLiveHazard reward strategy)

omit [DecidableEq ι] in
@[simp] theorem quittingBehaviorStoppingLaw_none_toReal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {who : ι} (strategy : (quittingGame reward).BehaviorStrategy who) :
    (quittingBehaviorStoppingLaw reward strategy none).toReal =
      quittingHazardNeverMass
        (quittingBehaviorLiveHazard reward strategy) := by
  simp [quittingBehaviorStoppingLaw]

omit [DecidableEq ι] in
@[simp] theorem quittingBehaviorStoppingLaw_some_toReal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {who : ι} (strategy : (quittingGame reward).BehaviorStrategy who)
    (time : ℕ) :
    (quittingBehaviorStoppingLaw reward strategy (some time)).toReal =
      quittingHazardStopMass
        (quittingBehaviorLiveHazard reward strategy) time := by
  simp [quittingBehaviorStoppingLaw]

end GameTheory
