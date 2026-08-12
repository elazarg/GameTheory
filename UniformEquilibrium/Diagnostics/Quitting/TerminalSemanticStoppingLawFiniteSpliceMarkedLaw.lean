/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawFiniteSplice

/-!
# Marked terminal-law stability under finite stopping-law splices

This module closes the terminal-law port of finite stopping-law capping.  An
arbitrary event of the complete terminal outcome space, including `Never`,
changes by at most twice the dimensionless splice error.  An outer complete
stopping-law mixture multiplies this bound by its literal mixture weight.

The factor two comes from the existing bounded terminal-value perturbation
estimate applied to a zero-one event reward.  No signed law difference is
reinterpreted as positive incidence, and no deletion or equilibrium theorem
is asserted.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Terminal laws depend only on the canonical live roots -/

omit [DecidableEq ι] in
/-- Complete terminal outcome probability is independent of the numerical
reward table once the canonical live-root sequence is fixed. -/
theorem quittingTerminalOutcomeMass_eq_of_profileLiveRoot_eq
    (firstReward secondReward :
      {S : Finset ι // S.Nonempty} → Payoff ι)
    (firstProfile : (quittingGame firstReward).BehaviorProfile)
    (secondProfile : (quittingGame secondReward).BehaviorProfile)
    (hroot : quittingProfileLiveRoot firstReward firstProfile =
      quittingProfileLiveRoot secondReward secondProfile)
    (outcome : QuittingTerminalOutcome ι) :
    quittingTerminalOutcomeMass firstReward firstProfile outcome =
      quittingTerminalOutcomeMass secondReward secondProfile outcome := by
  classical
  cases outcome with
  | none =>
      change quittingLiveMassLimit firstReward firstProfile =
        quittingLiveMassLimit secondReward secondProfile
      unfold quittingLiveMassLimit
      congr 1
      funext time
      rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
        quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot, hroot]
  | some terminal =>
      rw [quittingTerminalOutcomeMass_eq_timeDisintegration,
        quittingTerminalOutcomeMass_eq_timeDisintegration]
      apply tsum_congr
      intro time
      rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
        quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
        quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
        quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot, hroot]

/-! ## Event indicators -/

/-- Probability assigned by a complete terminal outcome law to a finite
event. -/
def quittingTerminalOutcomeEventMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (event : Finset (QuittingTerminalOutcome ι)) : ℝ :=
  ∑ outcome ∈ event, quittingTerminalOutcomeMass reward profile outcome

/-- Zero-one terminal reward representing the finite absorbing outcomes of
an event.  The `Never` coordinate is handled separately by complementation.
-/
def quittingTerminalOutcomeEventReward
    (event : Finset (QuittingTerminalOutcome ι)) :
    {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun terminal _ => if some terminal ∈ event then 1 else 0

omit [Fintype ι] in
theorem quittingTerminalOutcomeEventReward_abs_le_one
    (event : Finset (QuittingTerminalOutcome ι))
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι) :
    |quittingTerminalOutcomeEventReward event terminal player| ≤ 1 := by
  unfold quittingTerminalOutcomeEventReward
  split_ifs <;> norm_num

/-- An event not containing `Never` is exactly the terminal payoff of its
zero-one reward table evaluated on any root-sequence realization of the
original live roots. -/
theorem quittingTerminalOutcomeEventMass_eq_rootSequenceTerminalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (event : Finset (QuittingTerminalOutcome ι))
    (hnone : none ∉ event) (observer : ι) :
    quittingTerminalOutcomeEventMass reward profile event =
      quittingRootSequenceTerminalValue
        (quittingTerminalOutcomeEventReward event)
        (quittingProfileLiveRoot reward profile) observer 0 := by
  let eventReward := quittingTerminalOutcomeEventReward event
  let rootProfile := quittingRootSequenceProfile eventReward
    (quittingProfileLiveRoot reward profile) 0
  have hlaw : ∀ outcome,
      quittingTerminalOutcomeMass reward profile outcome =
        quittingTerminalOutcomeMass eventReward rootProfile outcome := by
    intro outcome
    apply quittingTerminalOutcomeMass_eq_of_profileLiveRoot_eq
    exact (quittingProfileLiveRoot_quittingRootSequenceProfile_zero
      eventReward (quittingProfileLiveRoot reward profile)).symm
  have hmoment := congrFun
    (quittingTerminalRewardMoment_outcomeMass eventReward rootProfile) observer
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingProfileLiveRoot_quittingRootSequenceProfile_zero] at hmoment
  rw [← hmoment]
  unfold quittingTerminalOutcomeEventMass quittingTerminalRewardMoment
  rw [show
      (∑ outcome ∈ event,
        quittingTerminalOutcomeMass reward profile outcome) =
      ∑ outcome : QuittingTerminalOutcome ι,
        if outcome ∈ event then
          quittingTerminalOutcomeMass reward profile outcome else 0 by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext outcome
      simp
    · intros
      rfl]
  simp only [quittingTerminalOutcomeReward]
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only [eventReward, Pi.zero_apply, mul_zero, zero_add,
    quittingTerminalOutcomeEventReward]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [if_neg hnone]
  simp only [zero_add]
  apply Finset.sum_congr rfl
  intro terminal _
  by_cases hmem : some terminal ∈ event
  · simp only [hmem, if_true]
    simpa only [eventReward] using hlaw (some terminal)
  · simp only [hmem, if_false]

/-- Event masses of a complete terminal law and its complement add to one.
-/
theorem quittingTerminalOutcomeEventMass_add_compl
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (event : Finset (QuittingTerminalOutcome ι)) :
    quittingTerminalOutcomeEventMass reward profile event +
      quittingTerminalOutcomeEventMass reward profile eventᶜ = 1 := by
  unfold quittingTerminalOutcomeEventMass
  rw [← Finset.sum_union]
  · simpa using (quittingTerminalOutcomeMass_mem_stdSimplex reward profile).2
  · exact Finset.disjoint_left.2 fun outcome houtcome hcompl =>
      (Finset.mem_compl.mp hcompl) houtcome

/-! ## Endpoint cap and lambda-scaled marked-law bounds -/

/-- Every event of the complete terminal law, including events containing
`Never`, is stable under finite capping. -/
theorem abs_quittingTerminalOutcomeEventMass_finiteCap_sub_le
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (strategy : (quittingGame reward).BehaviorStrategy mover)
    (cutoff : ℕ) (event : Finset (QuittingTerminalOutcome ι)) :
    |quittingTerminalOutcomeEventMass reward
          (Function.update profile mover strategy) event -
        quittingTerminalOutcomeEventMass reward
          (Function.update profile mover
            (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
              cutoff)) event| ≤
      2 * quittingFiniteSpliceError
        (quittingProfileLiveRoot reward profile) mover
          (quittingBehaviorLiveHazard reward strategy) cutoff := by
  by_cases hnone : none ∈ event
  · have hfirst := quittingTerminalOutcomeEventMass_add_compl reward
      (Function.update profile mover strategy) event
    have hsecond := quittingTerminalOutcomeEventMass_add_compl reward
      (Function.update profile mover
        (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
          cutoff)) event
    have hcomplNone : none ∉ eventᶜ := by simp [hnone]
    have hbound := abs_quittingRootSequenceTerminalValue_finiteCap_sub_le_max
      (quittingTerminalOutcomeEventReward eventᶜ)
      (quittingProfileLiveRoot reward profile) mover mover
      (quittingBehaviorLiveHazard reward strategy) cutoff
      (M := 1) (by norm_num)
      (quittingTerminalOutcomeEventReward_abs_le_one eventᶜ)
    have hsourceEvent :=
      quittingTerminalOutcomeEventMass_eq_rootSequenceTerminalValue
        reward (Function.update profile mover strategy) eventᶜ hcomplNone mover
    rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate] at hsourceEvent
    have hcapEvent :=
      quittingTerminalOutcomeEventMass_eq_rootSequenceTerminalValue
        reward
          (Function.update profile mover
            (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
              cutoff)) eventᶜ hcomplNone mover
    rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
      quittingBehaviorLiveHazard_finiteCap] at hcapEvent
    rw [← hsourceEvent, ← hcapEvent] at hbound
    have heq :
        quittingTerminalOutcomeEventMass reward
              (Function.update profile mover strategy) event -
            quittingTerminalOutcomeEventMass reward
              (Function.update profile mover
                (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                  cutoff)) event =
          -(quittingTerminalOutcomeEventMass reward
              (Function.update profile mover strategy) eventᶜ -
            quittingTerminalOutcomeEventMass reward
              (Function.update profile mover
                (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                  cutoff)) eventᶜ) := by
      linarith
    rw [heq, abs_neg]
    simpa [quittingFiniteSpliceError] using hbound
  · have hbound := abs_quittingRootSequenceTerminalValue_finiteCap_sub_le_max
      (quittingTerminalOutcomeEventReward event)
      (quittingProfileLiveRoot reward profile) mover mover
      (quittingBehaviorLiveHazard reward strategy) cutoff
      (M := 1) (by norm_num)
      (quittingTerminalOutcomeEventReward_abs_le_one event)
    have hsourceEvent :=
      quittingTerminalOutcomeEventMass_eq_rootSequenceTerminalValue
        reward (Function.update profile mover strategy) event hnone mover
    rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate] at hsourceEvent
    have hcapEvent :=
      quittingTerminalOutcomeEventMass_eq_rootSequenceTerminalValue
        reward
          (Function.update profile mover
            (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
              cutoff)) event hnone mover
    rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
      quittingBehaviorLiveHazard_finiteCap] at hcapEvent
    rw [← hsourceEvent, ← hcapEvent] at hbound
    simpa [quittingFiniteSpliceError] using hbound

/-- An outer complete stopping-law mixture scales every marked-law event
error by its literal mixture weight. -/
theorem quittingTerminalOutcomeEventMass_stoppingLawMixture_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (event : Finset (QuittingTerminalOutcome ι)) :
    quittingTerminalOutcomeEventMass reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            lambda hlambda0 hlambda1)) event =
      (1 - lambda) * quittingTerminalOutcomeEventMass reward
          (Function.update profile mover source) event +
        lambda * quittingTerminalOutcomeEventMass reward
          (Function.update profile mover target) event := by
  unfold quittingTerminalOutcomeEventMass
  simp_rw [quittingTerminalOutcomeMass_stoppingLawMixture_eq]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

theorem abs_quittingTerminalOutcomeEventMass_mixtureFiniteCap_sub_le
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (cutoff : ℕ) (event : Finset (QuittingTerminalOutcome ι)) :
    |quittingTerminalOutcomeEventMass reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              lambda hlambda0 hlambda1)) event -
        quittingTerminalOutcomeEventMass reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover target
                cutoff) lambda hlambda0 hlambda1)) event| ≤
      lambda * (2 * quittingFiniteSpliceError
        (quittingProfileLiveRoot reward profile) mover
          (quittingBehaviorLiveHazard reward target) cutoff) := by
  rw [quittingTerminalOutcomeEventMass_stoppingLawMixture_eq
      reward profile mover source target lambda hlambda0 hlambda1 event,
    quittingTerminalOutcomeEventMass_stoppingLawMixture_eq
      reward profile mover source
        (quittingStoppingLawFiniteCapBehaviorStrategy reward mover target cutoff)
        lambda hlambda0 hlambda1 event,
    show
      ((1 - lambda) * quittingTerminalOutcomeEventMass reward
          (Function.update profile mover source) event +
        lambda * quittingTerminalOutcomeEventMass reward
          (Function.update profile mover target) event) -
      ((1 - lambda) * quittingTerminalOutcomeEventMass reward
          (Function.update profile mover source) event +
        lambda * quittingTerminalOutcomeEventMass reward
          (Function.update profile mover
            (quittingStoppingLawFiniteCapBehaviorStrategy reward mover target
              cutoff)) event) =
      lambda *
        (quittingTerminalOutcomeEventMass reward
            (Function.update profile mover target) event -
          quittingTerminalOutcomeEventMass reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover target
                cutoff)) event) by ring,
    abs_mul, abs_of_nonneg hlambda0]
  exact mul_le_mul_of_nonneg_left
    (abs_quittingTerminalOutcomeEventMass_finiteCap_sub_le
      reward profile mover target cutoff event) hlambda0

/-! ## Cap-tight marked-event retention -/

/-- Along a cap-tight sequence, one can choose finite cutoffs tending to
infinity so that every retained marked event loses at most its literal
`2 * lambda * spliceError` amount.  This is a law-retention statement only;
it does not turn the signed comparison into positive incidence. -/
theorem exists_finiteSpliceCutoffs_markedEvent_retained_of_capTight
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι)
    (source target : ℕ → (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℕ → ℝ)
    (hlambda0 : ∀ n, 0 ≤ lambda n) (hlambda1 : ∀ n, lambda n ≤ 1)
    (event : Finset (QuittingTerminalOutcome ι)) (rho : ℝ)
    (hretained : ∀ n,
      rho ≤ quittingTerminalOutcomeEventMass reward
        (Function.update (profile n) mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover
            (source n) (target n) (lambda n) (hlambda0 n) (hlambda1 n)))
        event)
    (hcap : Tendsto (fun n =>
      quittingHazardNeverMass
          (quittingBehaviorLiveHazard reward (target n)) *
        quittingMaxPairDeletedSurvivalLimit
          (quittingProfileLiveRoot reward (profile n)) mover 0)
      atTop (nhds 0)) :
    ∃ cutoffs : ℕ → ℕ,
      Tendsto cutoffs atTop atTop ∧
      Tendsto (fun n =>
        quittingFiniteSpliceError
          (quittingProfileLiveRoot reward (profile n)) mover
          (quittingBehaviorLiveHazard reward (target n)) (cutoffs n))
        atTop (nhds 0) ∧
      ∀ n,
        rho - lambda n *
            (2 * quittingFiniteSpliceError
              (quittingProfileLiveRoot reward (profile n)) mover
              (quittingBehaviorLiveHazard reward (target n)) (cutoffs n)) ≤
          quittingTerminalOutcomeEventMass reward
            (Function.update (profile n) mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                (source n)
                (quittingStoppingLawFiniteCapBehaviorStrategy reward mover
                  (target n) (cutoffs n))
                (lambda n) (hlambda0 n) (hlambda1 n))) event := by
  obtain ⟨cutoffs, hcutoffs, herror⟩ :=
    exists_finiteSpliceCutoffs_tendsto_zero_of_capTight
      (fun n => quittingProfileLiveRoot reward (profile n)) mover
      (fun n => quittingBehaviorLiveHazard reward (target n)) hcap
  refine ⟨cutoffs, hcutoffs, herror, fun n => ?_⟩
  have hbound :=
    abs_quittingTerminalOutcomeEventMass_mixtureFiniteCap_sub_le
      reward (profile n) mover (source n) (target n) (lambda n)
        (hlambda0 n) (hlambda1 n) (cutoffs n) event
  have hside := le_abs_self
    (quittingTerminalOutcomeEventMass reward
        (Function.update (profile n) mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover
            (source n) (target n) (lambda n) (hlambda0 n) (hlambda1 n)))
        event -
      quittingTerminalOutcomeEventMass reward
        (Function.update (profile n) mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover
            (source n)
            (quittingStoppingLawFiniteCapBehaviorStrategy reward mover
              (target n) (cutoffs n))
            (lambda n) (hlambda0 n) (hlambda1 n))) event)
  linarith [hretained n]

end GameTheory
