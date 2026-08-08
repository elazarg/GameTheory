/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.OccupationBehaviorRealization
import UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.BellmanAccountIdentity

/-!
# Full-history player-neutral occupation accounts

A unilateral behavior strategy may depend on the complete public game
history, including past joint actions.  It therefore cannot in general be
represented by a selector on state histories alone.

This file realizes a selector on the actual type `G.Hist stage` directly.
All accounting is performed under the resulting `G.histDist`; no Markov
claim is made for the projected state process.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Math Math.PMFProduct Math.Probability Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- Full-history owner strategy realizing a predictable selector of active
player-neutral occupation rows. -/
def historyOccupationBehaviorStrategy
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, G.Hist stage →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active}) :
    G.BehaviorStrategy who :=
  fun stage history =>
    (selection stage history).bind
      (fixedOccupationActionDist germ ht who)

/-- Actual profile induced by a full-history occupation selector. -/
def realizedHistoryOccupationProfile
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, G.Hist stage →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active}) :
    G.BehaviorProfile :=
  Function.update
    (G.scheduledMarkovBehaviorProfile
      (fun _ source =>
        G.finkProfile (germ.finkPointAt ht) source))
    who
    (historyOccupationBehaviorStrategy
      germ ht who active selection)

omit [DecidableEq G.State] in
/-- At every complete public history, the actual one-step state kernel is
the selector mixture of the semantic player-neutral kernels. -/
theorem behaviorStateStep_realizedHistoryOccupationProfile
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, G.Hist stage →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (source_compatible :
      ∀ stage history index,
        selection stage history index ≠ 0 →
          germ.playerNeutralOccupationSource who index.1 =
            history.2)
    {stage : ℕ} (history : G.Hist stage) :
    LowerValueJet.behaviorStateStep
        (germ.realizedHistoryOccupationProfile
          ht who active selection)
        history =
      (selection stage history).bind
        (fun index =>
          germ.finkPlayerNeutralOccupationKernelAt
            ht who index.1) := by
  unfold LowerValueJet.behaviorStateStep
    realizedHistoryOccupationProfile
  change
    (G.stageActionDist
      (Function.update
        (G.scheduledMarkovBehaviorProfile
          (fun _ source =>
            G.finkProfile (germ.finkPointAt ht) source))
        who
        (historyOccupationBehaviorStrategy
          germ ht who active selection))
      history).bind (G.transition history.2) =
      (selection stage history).bind
        (fun index =>
          germ.finkPlayerNeutralOccupationKernelAt
            ht who index.1)
  rw [G.stageActionDist_update_scheduledMarkovBehaviorProfile]
  unfold historyOccupationBehaviorStrategy
  rw [pmfPi_update_bind, PMF.bind_bind, PMF.bind_bind]
  apply ProbabilityMassFunction.bind_congr_on_support
  intro index index_mem
  have source_eq :
      germ.playerNeutralOccupationSource who index.1 =
        history.2 :=
    source_compatible stage history index index_mem
  rw [← source_eq]
  rw [← PMF.bind_bind, ← pmfPi_update_bind]
  exact fixedOccupationActionDist_bind_transition
    germ ht who index

omit [DecidableEq G.State] in
private theorem fixedOccupation_stageEU_eq
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι)
    {active : Finset (germ.PlayerNeutralOccupationIndex who)}
    (index :
      {index : germ.PlayerNeutralOccupationIndex who //
        index ∈ active}) :
    G.mixedStageEU
          (germ.playerNeutralOccupationSource who index.1)
          (Function.update
            (G.finkProfile (germ.finkPointAt ht)
              (germ.playerNeutralOccupationSource who index.1))
            who
            (fixedOccupationActionDist germ ht who index))
          who =
      germ.playerNeutralOccupationStageEUAt ht who index.1 := by
  rcases index with ⟨index, membership⟩
  cases index with
  | inl source =>
      simp only [playerNeutralOccupationSource,
        fixedOccupationActionDist,
        playerNeutralOccupationStageEUAt]
      rw [Function.update_eq_self]
      unfold finkStageEU mixedStageEU
      rfl
  | inr response =>
      rfl

omit [DecidableEq G.State] in
private theorem realizedHistoryOccupation_stageEU_eq_selector
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, G.Hist stage →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (source_compatible :
      ∀ stage history index,
        selection stage history index ≠ 0 →
          germ.playerNeutralOccupationSource who index.1 =
            history.2)
    {stage : ℕ} (history : G.Hist stage) :
    G.stageEUAt
        (germ.realizedHistoryOccupationProfile
          ht who active selection)
        history who =
      expect (selection stage history)
        (fun index =>
          germ.playerNeutralOccupationStageEUAt
            ht who index.1) := by
  unfold stageEUAt realizedHistoryOccupationProfile
  rw [G.stageActionDist_update_scheduledMarkovBehaviorProfile]
  unfold historyOccupationBehaviorStrategy
  rw [pmfPi_update_bind, expect_bind, expect_bind]
  apply ProbabilityMassFunction.expect_congr_on_support
  intro index index_mem
  have source_eq :
      germ.playerNeutralOccupationSource who index.1 =
        history.2 :=
    source_compatible stage history index index_mem
  rw [← source_eq]
  rw [← expect_bind, ← pmfPi_update_bind]
  exact fixedOccupation_stageEU_eq germ ht who index

omit [Fintype G.State] [DecidableEq ι] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)] in
/-- A state-only history potential has continuation expectation equal to
expectation under the actual one-step state kernel. -/
theorem historyContinuationEU_statePotential_eq_behaviorStateStep
    [Finite G.State]
    (profile : G.BehaviorProfile) (potential : G.State → ℝ)
    {stage : ℕ} (history : G.Hist stage) :
    G.historyContinuationEU profile
        (fun _ nextHistory => potential nextHistory.2)
        history =
      expect
        (LowerValueJet.behaviorStateStep profile history)
        potential := by
  unfold historyContinuationEU LowerValueJet.behaviorStateStep
  rw [expect_bind]

/-- Realized stage-plus-`B` continuation gain over the frozen prescribed
Fink row at the same current source. -/
def realizedHistoryOccupationBellmanGainAt
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, G.Hist stage →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    {stage : ℕ} (history : G.Hist stage) : ℝ :=
  let profile :=
    germ.realizedHistoryOccupationProfile
      ht who active selection
  G.stageEUAt profile history who +
      expect
        (LowerValueJet.behaviorStateStep profile history)
        (fun successor => B successor who) -
    (G.finkStageEU (germ.finkPointAt ht) history.2 who +
      G.finkContinuationEU B
        (germ.finkPointAt ht) history.2 who)

omit [DecidableEq G.State] in
/-- Under a full-history selector, the realized one-step Bellman gain is
still exactly the selector expectation of the moving raw charge. -/
theorem realizedHistoryOccupationBellmanGainAt_eq_rawCharge
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, G.Hist stage →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (source_compatible :
      ∀ stage history index,
        selection stage history index ≠ 0 →
          germ.playerNeutralOccupationSource who index.1 =
            history.2)
    {stage : ℕ} (history : G.Hist stage) :
    germ.realizedHistoryOccupationBellmanGainAt
        B ht who active selection history =
      expect (selection stage history)
        (fun index =>
          germ.rawPlayerNeutralOccupationCharge
            B who t index.1) := by
  dsimp only [realizedHistoryOccupationBellmanGainAt]
  rw [
    realizedHistoryOccupation_stageEU_eq_selector
      germ ht who active selection source_compatible history]
  rw [
    germ.behaviorStateStep_realizedHistoryOccupationProfile
      ht who active selection source_compatible history,
    expect_bind]
  rw [← expect_add]
  rw [← expect_const
    (selection stage history)
    (G.finkStageEU (germ.finkPointAt ht) history.2 who +
      G.finkContinuationEU B
        (germ.finkPointAt ht) history.2 who)]
  rw [← expect_sub]
  apply ProbabilityMassFunction.expect_congr_on_support
  intro index index_mem
  have source_eq :
      germ.playerNeutralOccupationSource who index.1 =
        history.2 :=
    source_compatible stage history index index_mem
  have identity :=
    germ.playerNeutralOccupation_bellmanAccount_eq
      B ht who index.1
  rw [← source_eq]
  linarith

omit [DecidableEq G.State] in
/-- Selector-averaged raw charge is bounded by the actual one-step drift of
`C`, without projecting the full-history law to a Markov state law. -/
theorem realizedHistoryOccupation_rawCharge_le_statePotentialDrift
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, G.Hist stage →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (source_compatible :
      ∀ stage history index,
        selection stage history index ≠ 0 →
          germ.playerNeutralOccupationSource who index.1 =
            history.2)
    (C : G.State → ℝ)
    (hcharge :
      ∀ index :
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active},
        germ.rawPlayerNeutralOccupationCharge B who t index.1 ≤
          transitionPotentialDrift
            (fun activeIndex =>
              germ.finkPlayerNeutralOccupationKernelAt
                ht who activeIndex.1)
            (fun activeIndex =>
              germ.playerNeutralOccupationSource who activeIndex.1)
            C index)
    {stage : ℕ} (history : G.Hist stage) :
    expect (selection stage history)
        (fun index =>
          germ.rawPlayerNeutralOccupationCharge B who t index.1) ≤
      expect
          (LowerValueJet.behaviorStateStep
            (germ.realizedHistoryOccupationProfile
              ht who active selection)
            history)
          C -
        C history.2 := by
  calc
    expect (selection stage history)
          (fun index =>
            germ.rawPlayerNeutralOccupationCharge
              B who t index.1) ≤
        expect (selection stage history)
          (transitionPotentialDrift
            (fun activeIndex =>
              germ.finkPlayerNeutralOccupationKernelAt
                ht who activeIndex.1)
            (fun activeIndex =>
              germ.playerNeutralOccupationSource who activeIndex.1)
            C) :=
      expect_mono (selection stage history) _ _ hcharge
    _ = expect
          ((selection stage history).bind
            (fun index =>
              germ.finkPlayerNeutralOccupationKernelAt
                ht who index.1))
          C -
        C history.2 := by
      let kernel :
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active} → PMF G.State :=
        fun index =>
          germ.finkPlayerNeutralOccupationKernelAt
            ht who index.1
      let source :
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active} → G.State :=
        fun index =>
          germ.playerNeutralOccupationSource who index.1
      have mixed :=
        expect_transitionPotentialDrift_eq_mixedDrift
          kernel source C (selection stage history) history.2
          (source_compatible stage history)
      exact mixed
    _ = expect
          (LowerValueJet.behaviorStateStep
            (germ.realizedHistoryOccupationProfile
              ht who active selection)
            history)
          C -
        C history.2 := by
      rw [
        germ.behaviorStateStep_realizedHistoryOccupationProfile
          ht who active selection source_compatible history]

/-- Expected raw charge at a complete public history. -/
def realizedHistoryOccupationExpectedCharge
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, G.Hist stage →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (t : ℝ) : G.HistoryPotential :=
  fun stage history =>
    expect (selection stage history)
      (fun index =>
        germ.rawPlayerNeutralOccupationCharge B who t index.1)

omit [DecidableEq G.State] in
/-- Fixed-horizon expected cumulative raw charge is paid directly on the
actual full game-history law by the endpoint motion of `C`. -/
theorem expected_realizedHistoryOccupationChargeSum_le
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, G.Hist stage →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (source_compatible :
      ∀ stage history index,
        selection stage history index ≠ 0 →
          germ.playerNeutralOccupationSource who index.1 =
            history.2)
    (C : G.State → ℝ)
    (hcharge :
      ∀ index :
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active},
        germ.rawPlayerNeutralOccupationCharge B who t index.1 ≤
          transitionPotentialDrift
            (fun activeIndex =>
              germ.finkPlayerNeutralOccupationKernelAt
                ht who activeIndex.1)
            (fun activeIndex =>
              germ.playerNeutralOccupationSource who activeIndex.1)
            C index)
    (initial : G.State) (total : ℕ) :
    (∑ stage ∈ Finset.range total,
      G.expectedHistoryValue
        (germ.realizedHistoryOccupationProfile
          ht who active selection)
        initial
        (germ.realizedHistoryOccupationExpectedCharge
          B who active selection t)
        stage) ≤
      2 * finiteStatePotentialBound C := by
  let profile :=
    germ.realizedHistoryOccupationProfile
      ht who active selection
  let charge :=
    germ.realizedHistoryOccupationExpectedCharge
      B who active selection t
  let potential : G.HistoryPotential :=
    fun _ history => C history.2
  have drift :
      ∀ stage (history : G.Hist stage),
        charge stage history ≤
          G.historyContinuationEU profile potential history -
            potential stage history := by
    intro stage history
    have h :=
      germ.realizedHistoryOccupation_rawCharge_le_statePotentialDrift
        B ht who active selection source_compatible
        C hcharge history
    rw [
      historyContinuationEU_statePotential_eq_behaviorStateStep
        profile C history]
    exact h
  have step (stage : ℕ) :
      G.expectedHistoryValue profile initial charge stage ≤
        G.expectedHistoryValue profile initial potential (stage + 1) -
          G.expectedHistoryValue profile initial potential stage :=
    G.expectedHistoryValue_drift_ge
      profile initial charge potential drift stage
  have telescope :
      (∑ stage ∈ Finset.range total,
          G.expectedHistoryValue profile initial charge stage) ≤
        G.expectedHistoryValue profile initial potential total -
          G.expectedHistoryValue profile initial potential 0 := by
    induction total with
    | zero => simp
    | succ total inductionHypothesis =>
        rw [Finset.sum_range_succ]
        linarith [step total]
  have potential_bound (stage : ℕ) :
      |G.expectedHistoryValue profile initial potential stage| ≤
        finiteStatePotentialBound C := by
    apply abs_expect_le_of_abs_le
    intro history
    simpa [potential, statePotentialAccount] using
      abs_statePotentialAccount_le_finiteStatePotentialBound
        C (fun _ => history.2) 0
  have initial_bound := potential_bound 0
  have final_bound := potential_bound total
  change
    (∑ stage ∈ Finset.range total,
      G.expectedHistoryValue profile initial charge stage) ≤
        2 * finiteStatePotentialBound C
  rw [abs_le] at initial_bound final_bound
  linarith

/-- Prescribed Fink baseline residual left after the full-history neutral
charge has been paid by the drift of `C`. -/
def historyPrescribedFinkBellmanResidualAt
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) (target : ℝ) (source : G.State) : ℝ :=
  G.finkStageEU (germ.finkPointAt ht) source who +
    G.finkContinuationEU B (germ.finkPointAt ht) source who -
    B source who - target

/-- Corrected history potential for the full-history neutral account. -/
def realizedHistoryOccupationAccountPotential
    (B : G.State → Payoff ι) (who : ι)
    (C : G.State → ℝ) : G.HistoryPotential :=
  fun _ history => B history.2 who - C history.2

omit [DecidableEq G.State] in
/-- The actual full-history profile satisfies the corrected `B - C`
Bellman inequality with only the prescribed baseline residual remaining. -/
theorem realizedHistoryOccupation_historyBellmanAccount
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) (target : ℝ)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, G.Hist stage →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (source_compatible :
      ∀ stage history index,
        selection stage history index ≠ 0 →
          germ.playerNeutralOccupationSource who index.1 =
            history.2)
    (C : G.State → ℝ)
    (hcharge :
      ∀ index :
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active},
        germ.rawPlayerNeutralOccupationCharge B who t index.1 ≤
          transitionPotentialDrift
            (fun activeIndex =>
              germ.finkPlayerNeutralOccupationKernelAt
                ht who activeIndex.1)
            (fun activeIndex =>
              germ.playerNeutralOccupationSource who activeIndex.1)
            C index)
    {stage : ℕ} (history : G.Hist stage) :
    G.stageEUAt
          (germ.realizedHistoryOccupationProfile
            ht who active selection)
          history who +
        G.historyContinuationEU
          (germ.realizedHistoryOccupationProfile
            ht who active selection)
          (realizedHistoryOccupationAccountPotential B who C)
          history ≤
      target +
        realizedHistoryOccupationAccountPotential
          B who C stage history +
        germ.historyPrescribedFinkBellmanResidualAt
          B ht who target history.2 := by
  let profile :=
    germ.realizedHistoryOccupationProfile
      ht who active selection
  have hgain :=
    germ.realizedHistoryOccupationBellmanGainAt_eq_rawCharge
      B ht who active selection source_compatible history
  have hdrift :=
    germ.realizedHistoryOccupation_rawCharge_le_statePotentialDrift
      B ht who active selection source_compatible
      C hcharge history
  have hcontinuation :
      G.historyContinuationEU profile
          (realizedHistoryOccupationAccountPotential B who C)
          history =
        expect
            (LowerValueJet.behaviorStateStep profile history)
            (fun successor => B successor who) -
          expect
            (LowerValueJet.behaviorStateStep profile history)
            C := by
    calc
      G.historyContinuationEU profile
            (realizedHistoryOccupationAccountPotential B who C)
            history =
          expect
            (LowerValueJet.behaviorStateStep profile history)
            (fun successor => B successor who - C successor) := by
        exact
          historyContinuationEU_statePotential_eq_behaviorStateStep
            profile (fun successor => B successor who - C successor)
            history
      _ =
          expect
              (LowerValueJet.behaviorStateStep profile history)
              (fun successor => B successor who) -
            expect
              (LowerValueJet.behaviorStateStep profile history)
              C := by
        rw [expect_sub]
  dsimp only [realizedHistoryOccupationBellmanGainAt] at hgain
  change
    G.stageEUAt profile history who +
          expect
            (LowerValueJet.behaviorStateStep profile history)
            (fun successor => B successor who) -
          (G.finkStageEU
              (germ.finkPointAt ht) history.2 who +
            G.finkContinuationEU B
              (germ.finkPointAt ht) history.2 who) =
        expect (selection stage history)
          (fun index =>
            germ.rawPlayerNeutralOccupationCharge
              B who t index.1) at hgain
  change
    expect (selection stage history)
        (fun index =>
          germ.rawPlayerNeutralOccupationCharge B who t index.1) ≤
      expect
          (LowerValueJet.behaviorStateStep profile history)
          C -
        C history.2 at hdrift
  rw [hcontinuation]
  unfold historyPrescribedFinkBellmanResidualAt
    realizedHistoryOccupationAccountPotential
  linarith

omit [DecidableEq G.State] in
/-- The fixed-parameter full-history Bellman account gives an average-payoff
cap once its endpoint-plus-prescribed-residual account is bounded. -/
theorem finiteAveragePayoff_realizedHistoryOccupation_le_target_add
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) (target error : ℝ)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, G.Hist stage →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (source_compatible :
      ∀ stage history index,
        selection stage history index ≠ 0 →
          germ.playerNeutralOccupationSource who index.1 =
            history.2)
    (C : G.State → ℝ)
    (hcharge :
      ∀ index :
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active},
        germ.rawPlayerNeutralOccupationCharge B who t index.1 ≤
          transitionPotentialDrift
            (fun activeIndex =>
              germ.finkPlayerNeutralOccupationKernelAt
                ht who activeIndex.1)
            (fun activeIndex =>
              germ.playerNeutralOccupationSource who activeIndex.1)
            C index)
    (initial : G.State) {total : ℕ}
    (haccount :
      (total : ℝ)⁻¹ *
          (G.expectedHistoryValue
              (germ.realizedHistoryOccupationProfile
                ht who active selection)
              initial
              (realizedHistoryOccupationAccountPotential B who C) 0 -
            G.expectedHistoryValue
              (germ.realizedHistoryOccupationProfile
                ht who active selection)
              initial
              (realizedHistoryOccupationAccountPotential B who C)
              total +
            ∑ stage ∈ Finset.range total,
              G.expectedHistoryValue
                (germ.realizedHistoryOccupationProfile
                  ht who active selection)
                initial
                (fun _ history =>
                  germ.historyPrescribedFinkBellmanResidualAt
                    B ht who target history.2)
                stage) ≤
        error)
    (htotal : 0 < total) :
    G.finiteAveragePayoff initial total
        (germ.realizedHistoryOccupationProfile
          ht who active selection)
        who ≤
      target + error := by
  let profile :=
    germ.realizedHistoryOccupationProfile
      ht who active selection
  let potential :=
    realizedHistoryOccupationAccountPotential B who C
  let residual : G.HistoryPotential :=
    fun _ history =>
      germ.historyPrescribedFinkBellmanResidualAt
        B ht who target history.2
  have hbellman :
      ∀ stage (history : G.Hist stage),
        G.stageEUAt profile history who +
            G.historyContinuationEU profile potential history ≤
          (target + residual stage history) +
            potential stage history + 0 := by
    intro stage history
    have h :=
      germ.realizedHistoryOccupation_historyBellmanAccount
        B ht who target active selection source_compatible
        C hcharge history
    change
      G.stageEUAt profile history who +
          G.historyContinuationEU profile potential history ≤
        target + potential stage history + residual stage history at h
    linarith
  have telescope :=
    G.finitePayoff_telescope_of_history_bellman_ge
      profile initial who
      (fun stage history => target + residual stage history)
      potential (fun _ => 0) hbellman total
  have expected_target_residual (stage : ℕ) :
      G.expectedHistoryValue profile initial
          (fun stage history =>
            target + residual stage history)
          stage =
        target +
          G.expectedHistoryValue
            profile initial residual stage := by
    unfold expectedHistoryValue
    rw [expect_add, expect_const]
  simp_rw [expected_target_residual] at telescope
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at telescope
  have raw :
      (∑ stage ∈ Finset.range total,
          G.expectedStagePayoff profile initial stage who) ≤
        (total : ℝ) * target +
          (G.expectedHistoryValue profile initial potential 0 -
            G.expectedHistoryValue profile initial potential total +
            ∑ stage ∈ Finset.range total,
              G.expectedHistoryValue profile initial residual stage) := by
    linarith
  have total_real : (0 : ℝ) < total := by
    exact_mod_cast htotal
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  calc
    (total : ℝ)⁻¹ *
          ∑ stage ∈ Finset.range total,
            G.expectedStagePayoff profile initial stage who ≤
        (total : ℝ)⁻¹ *
          ((total : ℝ) * target +
            (G.expectedHistoryValue profile initial potential 0 -
              G.expectedHistoryValue profile initial potential total +
              ∑ stage ∈ Finset.range total,
                G.expectedHistoryValue
                  profile initial residual stage)) :=
      mul_le_mul_of_nonneg_left raw
        (inv_nonneg.mpr total_real.le)
    _ = target +
        (total : ℝ)⁻¹ *
          (G.expectedHistoryValue profile initial potential 0 -
            G.expectedHistoryValue profile initial potential total +
            ∑ stage ∈ Finset.range total,
                G.expectedHistoryValue
                  profile initial residual stage) := by
      field_simp [ne_of_gt total_real]
    _ ≤ target + error := by
      exact add_le_add (le_refl target)
        (by
          simpa only [profile, potential, residual] using haccount)

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
