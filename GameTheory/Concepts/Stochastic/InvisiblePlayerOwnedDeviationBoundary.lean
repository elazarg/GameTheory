/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PlayerOwnedBehaviorCalendarAccount

/-!
# Invisible player-owned deviations

At a positive point of an analytic Fink germ, a pure deviation whose
one-step state kernel is exactly the prescribed Fink kernel cannot improve
the current-stage payoff.  The discounted Bellman inequality has no
continuation term with which to pay for such an improvement.

The same statement survives arbitrary mixing over invisible pure rows.
This file records both the stationary one-step statement and its
public-history specialization for the universal Fink calendar.  It does
not make any assertion about transporting a full payoff target between
recurrent classes.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Math Math.OnlineLearning Math.PMFProduct Math.Probability
  Math.ProbabilityMassFunction Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

omit [DecidableEq G.State] in
/-- At a valid positive germ parameter, a pure deviation with the same
state kernel as the prescribed Fink profile has nonpositive current-stage
gain. -/
theorem finkStageGain_nonpos_of_pureDeviationStateKernel_eq
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (source : G.State) (who : ι) (action : G.Act who)
    (hkernel :
      G.finkPureDeviationStateKernel
          (germ.finkPointAt ht) source who action =
        G.finkStateKernel (germ.finkPointAt ht) source) :
    G.finkStageGain
        (germ.finkPointAt ht) source who action ≤ 0 := by
  have hgain :
      G.finkGain (1 - t ^ germ.ramification)
          (germ.finkPointAt ht) source who action ≤ 0 := by
    unfold finkGain
    rw [G.finkDeviationAuxEU_eq_discountedAuxEU,
      G.finkAuxEU_eq_discountedAuxEU]
    exact sub_nonpos.mpr
      ((germ.isDiscountedStationaryBellmanEq_finkPointAt ht).1
        source who (PMF.pure action))
  have hcontinuation :
      G.finkContinuationGain
          (G.finkValue (germ.finkPointAt ht))
          (germ.finkPointAt ht) source who action = 0 :=
    G.finkContinuationGain_eq_zero_of_pureDeviationStateKernel_eq
      (G.finkValue (germ.finkPointAt ht))
      (germ.finkPointAt ht) source who action hkernel
  rw [G.finkGain_eq_stage_add_continuation, hcontinuation] at hgain
  have hscale : 0 < t ^ germ.ramification := pow_pos ht.1 _
  simp only [mul_zero, add_zero, sub_sub_cancel] at hgain
  nlinarith

/-- The state kernel obtained by replacing one component of a decoded Fink
profile by an arbitrary mixed action. -/
def finkMixedDeviationStateKernel
    {U : ℝ} (z : G.finkDomain U) (source : G.State)
    (who : ι) (deviation : PMF (G.Act who)) : PMF G.State :=
  (pmfPi
      (Function.update (G.finkProfile z source) who deviation)).bind
    (G.transition source)

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- A mixed unilateral row is the mixture of its pure unilateral rows. -/
theorem finkMixedDeviationStateKernel_eq_bind_pure
    {U : ℝ} (z : G.finkDomain U) (source : G.State)
    (who : ι) (deviation : PMF (G.Act who)) :
    finkMixedDeviationStateKernel z source who deviation =
      deviation.bind fun action =>
        G.finkPureDeviationStateKernel z source who action := by
  unfold finkMixedDeviationStateKernel finkPureDeviationStateKernel
  rw [pmfPi_update_bind, PMF.bind_bind]

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- Mixing only pure rows equal to the prescribed state kernel leaves the
one-step state law unchanged. -/
theorem finkMixedDeviationStateKernel_eq_of_support_invisible
    {U : ℝ} (z : G.finkDomain U) (source : G.State)
    (who : ι) (deviation : PMF (G.Act who))
    (hinvisible :
      ∀ action ∈ deviation.support,
        G.finkPureDeviationStateKernel z source who action =
          G.finkStateKernel z source) :
    finkMixedDeviationStateKernel z source who deviation =
      G.finkStateKernel z source := by
  rw [finkMixedDeviationStateKernel_eq_bind_pure]
  rw [bind_congr_on_support deviation
    (fun action => G.finkPureDeviationStateKernel z source who action)
    (fun _ => G.finkStateKernel z source) hinvisible]
  simp

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- Current-stage payoff under a mixed unilateral row is the expectation
of the corresponding pure-row payoffs. -/
theorem mixedStageEU_update_eq_expect_pure
    {U : ℝ} (z : G.finkDomain U) (source : G.State)
    (who : ι) (deviation : PMF (G.Act who)) :
    G.mixedStageEU source
        (Function.update (G.finkProfile z source) who deviation) who =
      expect deviation fun action =>
        G.mixedStageEU source
          (Function.update (G.finkProfile z source)
            who (PMF.pure action)) who := by
  unfold mixedStageEU
  rw [pmfPi_update_bind, expect_bind]

omit [DecidableEq G.State] in
/-- A mixed deviation supported on invisible pure rows preserves the
one-step state kernel and cannot improve current-stage expected payoff. -/
theorem finkMixedDeviation_invisible
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (source : G.State) (who : ι)
    (deviation : PMF (G.Act who))
    (hinvisible :
      ∀ action ∈ deviation.support,
        G.finkPureDeviationStateKernel
            (germ.finkPointAt ht) source who action =
          G.finkStateKernel (germ.finkPointAt ht) source) :
    finkMixedDeviationStateKernel
          (germ.finkPointAt ht) source who deviation =
        G.finkStateKernel (germ.finkPointAt ht) source ∧
      G.mixedStageEU source
          (Function.update
            (G.finkProfile (germ.finkPointAt ht) source)
            who deviation) who ≤
        G.mixedStageEU source
          (G.finkProfile (germ.finkPointAt ht) source) who := by
  constructor
  · exact finkMixedDeviationStateKernel_eq_of_support_invisible
      (germ.finkPointAt ht) source who deviation hinvisible
  · rw [mixedStageEU_update_eq_expect_pure]
    apply expect_le_of_le_on_support
    intro action ha
    have hgain :=
      germ.finkStageGain_nonpos_of_pureDeviationStateKernel_eq
        ht source who action (hinvisible action ha)
    exact sub_nonpos.mp hgain

/-- The state law generated by a calendar-time state kernel. -/
def calendarStateDist
    (kernel : ℕ → G.State → PMF G.State)
    (initial : G.State) : ℕ → PMF G.State
  | 0 => PMF.pure initial
  | stage + 1 =>
      (calendarStateDist kernel initial stage).bind (kernel stage)

omit [Fintype G.State] [DecidableEq G.State] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)] in
/-- If a possibly history-dependent behavior profile has a one-step state
law depending only on calendar time and current state, then the state
marginal of its full history law follows that calendar kernel.  The full
history laws need not agree because actions remain publicly recorded. -/
theorem map_snd_histDist_eq_calendarStateDist
    (profile : G.BehaviorProfile)
    (kernel : ℕ → G.State → PMF G.State)
    (hstep :
      ∀ {stage : ℕ} (history : G.Hist stage),
        LowerValueJet.behaviorStateStep profile history =
          kernel stage history.2)
    (initial : G.State) :
    ∀ stage,
      (G.histDist profile initial stage).map Prod.snd =
        calendarStateDist kernel initial stage := by
  intro stage
  induction stage with
  | zero =>
      rw [G.histDist_zero, PMF.pure_map]
      rfl
  | succ stage ih =>
      rw [G.histDist_succ, PMF.map_bind]
      change
        (G.histDist profile initial stage).bind
            (fun history =>
              ((G.stageActionDist profile history).bind
                (fun actions =>
                  (G.transition history.2 actions).bind
                    (fun destination =>
                      PMF.pure
                        ((Fin.snoc history.1
                          (history.2, actions), destination) :
                            G.Hist (stage + 1))))).map Prod.snd) =
          calendarStateDist kernel initial (stage + 1)
      have hinner :
          ∀ history : G.Hist stage,
            ((G.stageActionDist profile history).bind
                (fun actions =>
                  (G.transition history.2 actions).bind
                    (fun destination =>
                      PMF.pure
                        ((Fin.snoc history.1
                          (history.2, actions), destination) :
                            G.Hist (stage + 1))))).map Prod.snd =
              kernel stage history.2 := by
        intro history
        rw [PMF.map_bind]
        change
          (G.stageActionDist profile history).bind
              (fun actions =>
                ((G.transition history.2 actions).bind
                  (fun destination =>
                    PMF.pure
                      ((Fin.snoc history.1
                        (history.2, actions), destination) :
                          G.Hist (stage + 1)))).map Prod.snd) =
            kernel stage history.2
        apply Eq.trans ?_ (hstep history)
        congr 1
        funext actions
        calc
          ((G.transition history.2 actions).bind
              (fun destination =>
                PMF.pure
                  ((Fin.snoc history.1
                    (history.2, actions), destination) :
                      G.Hist (stage + 1)))).map Prod.snd =
              (G.transition history.2 actions).bind
                (fun destination => PMF.pure destination) := by
                  rw [PMF.map_bind]
                  congr 1
                  funext destination
                  rw [PMF.pure_map]
          _ = G.transition history.2 actions := PMF.bind_pure _
      simp_rw [hinner]
      change
        (G.histDist profile initial stage).bind
            (kernel stage ∘ Prod.snd) =
          calendarStateDist kernel initial (stage + 1)
      rw [← PMF.bind_map, ih]
      rfl

omit [DecidableEq G.State] in
/-- Public-history specialization: if the behavior deviation mixes only
invisible player-owned rows at this history, its next-state law is the
prescribed Fink state kernel for the current calendar point. -/
theorem behaviorStateStep_scheduledPlayerOwned_eq_finkStateKernel_of_invisible
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    {stage : ℕ} (history : G.Hist stage)
    (hinvisible :
      ∀ action ∈ (dev stage history).support,
        G.finkPureDeviationStateKernel
            (germ.finkPointAt
              (valid (anytimeEpochIndex stage)))
            history.2 who action =
          G.finkStateKernel
            (germ.finkPointAt
              (valid (anytimeEpochIndex stage)))
            history.2) :
    LowerValueJet.behaviorStateStep
        (scheduledPlayerOwnedFinkDeviationProfile
          germ who startEpoch valid dev)
        history =
      G.finkStateKernel
        (germ.finkPointAt
          (valid (anytimeEpochIndex stage)))
        history.2 := by
  rw [behaviorStateStep_scheduledPlayerOwnedFinkDeviationProfile]
  unfold playerOwnedCalendarMixedStep
  change
    (dev stage history).bind
        (fun action =>
          G.finkPureDeviationStateKernel
            (germ.finkPointAt
              (valid (anytimeEpochIndex stage)))
            history.2 who action) =
      G.finkStateKernel
        (germ.finkPointAt
          (valid (anytimeEpochIndex stage)))
        history.2
  rw [bind_congr_on_support (dev stage history)
    (fun action =>
      G.finkPureDeviationStateKernel
        (germ.finkPointAt
          (valid (anytimeEpochIndex stage)))
        history.2 who action)
    (fun _ =>
      G.finkStateKernel
        (germ.finkPointAt
          (valid (anytimeEpochIndex stage)))
        history.2)
    hinvisible]
  simp

omit [DecidableEq G.State] in
/-- Public-history specialization of current-stage payoff domination for
a behavior deviation supported on invisible rows. -/
theorem stageEUAt_scheduledPlayerOwned_le_of_invisible
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    {stage : ℕ} (history : G.Hist stage)
    (hinvisible :
      ∀ action ∈ (dev stage history).support,
        G.finkPureDeviationStateKernel
            (germ.finkPointAt
              (valid (anytimeEpochIndex stage)))
            history.2 who action =
          G.finkStateKernel
            (germ.finkPointAt
              (valid (anytimeEpochIndex stage)))
            history.2) :
    G.stageEUAt
        (scheduledPlayerOwnedFinkDeviationProfile
          germ who startEpoch valid dev)
        history who ≤
      G.stageEUAt
        (G.scheduledMarkovBehaviorProfile
          (fun currentStage source =>
            G.finkProfile
              (germ.finkPointAt
                (valid (anytimeEpochIndex currentStage)))
              source))
        history who := by
  unfold stageEUAt scheduledPlayerOwnedFinkDeviationProfile
  rw [G.stageActionDist_update_scheduledMarkovBehaviorProfile]
  change
    G.mixedStageEU history.2
        (Function.update
          (G.finkProfile
            (germ.finkPointAt
              (valid (anytimeEpochIndex stage)))
            history.2)
          who (dev stage history)) who ≤
      G.mixedStageEU history.2
        (G.finkProfile
          (germ.finkPointAt
            (valid (anytimeEpochIndex stage)))
          history.2) who
  exact
    (germ.finkMixedDeviation_invisible
      (valid (anytimeEpochIndex stage))
      history.2 who (dev stage history) hinvisible).2

omit [DecidableEq G.State] in
/-- If invisibility holds after every public history, the deviating
profile's state marginal follows the prescribed calendar of Fink state
kernels.  This deliberately asserts only state-marginal equality, not
equality of the action-recording history distributions. -/
theorem map_snd_histDist_scheduledPlayerOwned_eq_calendarStateDist
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    (hinvisible :
      ∀ {stage : ℕ} (history : G.Hist stage)
          (action : G.Act who),
        action ∈ (dev stage history).support →
          G.finkPureDeviationStateKernel
              (germ.finkPointAt
                (valid (anytimeEpochIndex stage)))
              history.2 who action =
            G.finkStateKernel
              (germ.finkPointAt
                (valid (anytimeEpochIndex stage)))
              history.2)
    (initial : G.State) (stage : ℕ) :
    (G.histDist
        (scheduledPlayerOwnedFinkDeviationProfile
          germ who startEpoch valid dev)
        initial stage).map Prod.snd =
      calendarStateDist
        (fun currentStage source =>
          G.finkStateKernel
            (germ.finkPointAt
              (valid (anytimeEpochIndex currentStage)))
            source)
        initial stage := by
  apply map_snd_histDist_eq_calendarStateDist
  intro currentStage history
  exact
    behaviorStateStep_scheduledPlayerOwned_eq_finkStateKernel_of_invisible
      germ who startEpoch valid dev history
      (fun action ha => hinvisible history action ha)

omit [DecidableEq G.State] in
/-- The prescribed scheduled Fink profile has the same calendar state
marginal as every everywhere-invisible unilateral behavior deviation. -/
theorem map_snd_histDist_scheduledFink_eq_calendarStateDist
    (germ : G.AnalyticBellmanGerm)
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (initial : G.State) (stage : ℕ) :
    (G.histDist
        (G.scheduledMarkovBehaviorProfile
          (fun currentStage source =>
            G.finkProfile
              (germ.finkPointAt
                (valid (anytimeEpochIndex currentStage)))
              source))
        initial stage).map Prod.snd =
      calendarStateDist
        (fun currentStage source =>
          G.finkStateKernel
            (germ.finkPointAt
              (valid (anytimeEpochIndex currentStage)))
            source)
        initial stage := by
  apply map_snd_histDist_eq_calendarStateDist
  intro currentStage history
  unfold LowerValueJet.behaviorStateStep
  rw [G.stageActionDist_scheduledMarkovBehaviorProfile]
  rfl

omit [DecidableEq G.State] in
/-- An everywhere-invisible behavior deviation has no larger expected
payoff at any stage than prescribed scheduled Fink play.  State-marginal
equality is enough: full public histories may still record different
actions. -/
theorem expectedStagePayoff_scheduledPlayerOwned_le_of_invisible
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    (hinvisible :
      ∀ {stage : ℕ} (history : G.Hist stage)
          (action : G.Act who),
        action ∈ (dev stage history).support →
          G.finkPureDeviationStateKernel
              (germ.finkPointAt
                (valid (anytimeEpochIndex stage)))
              history.2 who action =
            G.finkStateKernel
              (germ.finkPointAt
                (valid (anytimeEpochIndex stage)))
              history.2)
    (initial : G.State) (stage : ℕ) :
    G.expectedStagePayoff
        (scheduledPlayerOwnedFinkDeviationProfile
          germ who startEpoch valid dev)
        initial stage who ≤
      G.expectedStagePayoff
        (G.scheduledMarkovBehaviorProfile
          (fun currentStage source =>
            G.finkProfile
              (germ.finkPointAt
                (valid (anytimeEpochIndex currentStage)))
              source))
        initial stage who := by
  let deviating :=
    scheduledPlayerOwnedFinkDeviationProfile
      germ who startEpoch valid dev
  let prescribed :=
    G.scheduledMarkovBehaviorProfile
      (fun currentStage source =>
        G.finkProfile
          (germ.finkPointAt
            (valid (anytimeEpochIndex currentStage)))
          source)
  let stageValue : G.State → ℝ := fun source =>
    G.mixedStageEU source
      (G.finkProfile
        (germ.finkPointAt
          (valid (anytimeEpochIndex stage)))
        source) who
  have hpoint :
      ∀ history : G.Hist stage,
        G.stageEUAt deviating history who ≤
          stageValue history.2 := by
    intro history
    have h :=
      stageEUAt_scheduledPlayerOwned_le_of_invisible
        germ who startEpoch valid dev history
        (fun action ha => hinvisible history action ha)
    simpa only [deviating, prescribed, stageValue, mixedStageEU,
      stageEUAt, stageActionDist_scheduledMarkovBehaviorProfile]
      using h
  have hdev :
      G.expectedStagePayoff deviating initial stage who ≤
        expect (G.histDist deviating initial stage)
          (fun history => stageValue history.2) := by
    unfold expectedStagePayoff
    exact expect_mono _ _ _ hpoint
  have hmarginal :
      (G.histDist deviating initial stage).map Prod.snd =
        (G.histDist prescribed initial stage).map Prod.snd := by
    rw [
      map_snd_histDist_scheduledPlayerOwned_eq_calendarStateDist
        germ who startEpoch valid dev hinvisible initial stage,
      map_snd_histDist_scheduledFink_eq_calendarStateDist
        germ startEpoch valid initial stage]
  calc
    G.expectedStagePayoff deviating initial stage who ≤
        expect (G.histDist deviating initial stage)
          (fun history => stageValue history.2) := hdev
    _ = expect ((G.histDist deviating initial stage).map Prod.snd)
          stageValue := by
      rw [expect_map]
    _ = expect ((G.histDist prescribed initial stage).map Prod.snd)
          stageValue := by rw [hmarginal]
    _ = expect (G.histDist prescribed initial stage)
          (fun history => stageValue history.2) := by
      rw [expect_map]
    _ = G.expectedStagePayoff prescribed initial stage who := by
      unfold expectedStagePayoff
      apply congrArg
      funext history
      simp only [prescribed, stageValue, mixedStageEU, stageEUAt,
        stageActionDist_scheduledMarkovBehaviorProfile]

omit [DecidableEq G.State] in
/-- Therefore every finite-horizon payoff of an everywhere-invisible
behavior deviation is bounded by prescribed scheduled Fink play.  The
remaining invisible-branch obligation is entirely on-path target
realization, not unilateral incentive control. -/
theorem finiteAveragePayoff_scheduledPlayerOwned_le_of_invisible
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    (hinvisible :
      ∀ {stage : ℕ} (history : G.Hist stage)
          (action : G.Act who),
        action ∈ (dev stage history).support →
          G.finkPureDeviationStateKernel
              (germ.finkPointAt
                (valid (anytimeEpochIndex stage)))
              history.2 who action =
            G.finkStateKernel
              (germ.finkPointAt
                (valid (anytimeEpochIndex stage)))
              history.2)
    (initial : G.State) (T : ℕ) :
    G.finiteAveragePayoff initial T
        (scheduledPlayerOwnedFinkDeviationProfile
          germ who startEpoch valid dev) who ≤
      G.finiteAveragePayoff initial T
        (G.scheduledMarkovBehaviorProfile
          (fun currentStage source =>
            G.finkProfile
              (germ.finkPointAt
                (valid (anytimeEpochIndex currentStage)))
              source)) who := by
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff,
    G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg T))
  exact Finset.sum_le_sum fun stage _ =>
    expectedStagePayoff_scheduledPlayerOwned_le_of_invisible
      germ who startEpoch valid dev hinvisible initial stage

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
