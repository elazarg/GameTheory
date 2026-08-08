/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.PuncturedPotentialCalendarAccount
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.Accounting.ProcessedHarmonicResponseRealization

/-!
# Behavioral realization of active player-neutral occupation mixtures

Fix one positive parameter of an analytic Fink germ and one player.  A
predictable selector over an active subtype of the player's occupation
indices is operationally realized as follows.

* a baseline index at the current source plays the prescribed Fink mixed
  action of the owner;
* a response index plays its player-owned pure action;
* every other player keeps the frozen Fink mixed action.

Source compatibility is retained explicitly.  Under this hypothesis, the
one-step state kernel of the resulting behavior profile is exactly the
selector mixture of the semantic occupation kernels.  Consequently, the
state-history marginal of the game history law is the abstract adaptive
history law used by the occupation account.

The realized stage-plus-continuation Bellman gain against a fixed bias is
also exactly the selector expectation of the moving raw occupation charge.
This identifies the existing fixed-epoch punctured-potential estimate with
an actual unilateral behavior strategy.

The selectors here depend only on public state histories.  A general public
behavior deviation may also depend on past public actions, in which case its
projected state law need not have this form.  A direct full-history account
is therefore separate.  This file also does not classify arbitrary
deviations, splice epochs, treat strict actions, or construct a punishment
certificate.
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

/-- Owner action distribution represented by one active player-neutral
occupation index at a fixed positive Fink parameter. -/
def fixedOccupationActionDist
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι)
    {active : Finset (germ.PlayerNeutralOccupationIndex who)}
    (index :
      {index : germ.PlayerNeutralOccupationIndex who //
        index ∈ active}) :
    PMF (G.Act who) :=
  match index.1 with
  | .inl source =>
      G.finkProfile (germ.finkPointAt ht) source who
  | .inr response => PMF.pure response.1.2

/-- The behavior strategy obtained by binding a predictable active-index
selector to the action distribution represented by the selected index. -/
def activeOccupationBehaviorStrategy
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active}) :
    G.BehaviorStrategy who :=
  fun stage history =>
    (selection stage
      (LowerValueJet.stateHistoryOfHist history)).bind
        (fixedOccupationActionDist germ ht who)

/-- The actual profile realizing a predictable active occupation mixture.
The owner realizes the selector and every other player follows the frozen
Fink profile. -/
def realizedActiveOccupationProfile
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active}) :
    G.BehaviorProfile :=
  Function.update
    (G.scheduledMarkovBehaviorProfile
      (fun _ source => G.finkProfile (germ.finkPointAt ht) source))
    who
    (activeOccupationBehaviorStrategy germ ht who active selection)

/-- The abstract selector mixture of the active moving occupation kernels. -/
def activeOccupationMixedStep
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι)
    {active : Finset (germ.PlayerNeutralOccupationIndex who)}
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (stage : ℕ) (history : Fin (stage + 1) → G.State) :
    PMF G.State :=
  mixedTransitionComparison
    (fun index =>
      germ.finkPlayerNeutralOccupationKernelAt ht who index.1)
    selection stage history

omit [DecidableEq G.State] in
/-- The action distribution represented by an index induces exactly its
semantic moving player-neutral occupation kernel. -/
theorem fixedOccupationActionDist_bind_transition
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι)
    {active : Finset (germ.PlayerNeutralOccupationIndex who)}
    (index :
      {index : germ.PlayerNeutralOccupationIndex who //
        index ∈ active}) :
    (pmfPi
        (Function.update
          (G.finkProfile (germ.finkPointAt ht)
            (germ.playerNeutralOccupationSource who index.1))
          who
          (fixedOccupationActionDist germ ht who index))).bind
      (G.transition
        (germ.playerNeutralOccupationSource who index.1)) =
      germ.finkPlayerNeutralOccupationKernelAt ht who index.1 := by
  rcases index with ⟨index, membership⟩
  cases index with
  | inl source =>
      simp only [fixedOccupationActionDist,
        playerNeutralOccupationSource,
        finkPlayerNeutralOccupationKernelAt,
        playerNeutralOccupationIndexEmbedding,
        finkActualOccupationKernelAt, occupationKernel]
      rw [Function.update_eq_self]
      rfl
  | inr response =>
      rfl

omit [DecidableEq G.State] in
/-- Exact one-step realization.  Source compatibility moves every selected
index to the current-state fiber before the PMF bind is compared. -/
theorem behaviorStateStep_realizedActiveOccupationProfile
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (source_compatible :
      ∀ stage history index,
        selection stage history index ≠ 0 →
          germ.playerNeutralOccupationSource who index.1 =
            history (Fin.last stage))
    {stage : ℕ} (history : G.Hist stage) :
    LowerValueJet.behaviorStateStep
        (realizedActiveOccupationProfile
          germ ht who active selection)
        history =
      activeOccupationMixedStep germ ht who selection stage
        (LowerValueJet.stateHistoryOfHist history) := by
  unfold LowerValueJet.behaviorStateStep
    realizedActiveOccupationProfile
  change
    (G.stageActionDist
      (Function.update
        (G.scheduledMarkovBehaviorProfile
          (fun _ source =>
            G.finkProfile (germ.finkPointAt ht) source))
        who
        (activeOccupationBehaviorStrategy
          germ ht who active selection))
      history).bind (G.transition history.2) =
      activeOccupationMixedStep germ ht who selection stage
        (LowerValueJet.stateHistoryOfHist history)
  rw [G.stageActionDist_update_scheduledMarkovBehaviorProfile]
  unfold activeOccupationBehaviorStrategy
    activeOccupationMixedStep mixedTransitionComparison
  rw [pmfPi_update_bind, PMF.bind_bind, PMF.bind_bind]
  apply ProbabilityMassFunction.bind_congr_on_support
  intro index index_mem
  have source_eq :
      germ.playerNeutralOccupationSource who index.1 =
        history.2 := by
    rw [← LowerValueJet.stateHistoryOfHist_last history]
    exact
      source_compatible stage
        (LowerValueJet.stateHistoryOfHist history)
        index index_mem
  rw [← source_eq]
  rw [← PMF.bind_bind, ← pmfPi_update_bind]
  exact fixedOccupationActionDist_bind_transition
    germ ht who index

/-- Public state-history marginal of the actual realized profile. -/
def realizedActiveOccupationStateHistoryLaw
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) (initial : G.State)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (stage : ℕ) :
    PMF (Fin (stage + 1) → G.State) :=
  (G.histDist
    (realizedActiveOccupationProfile
      germ ht who active selection)
    initial stage).map LowerValueJet.stateHistoryOfHist

omit [DecidableEq G.State] in
/-- One-step recursion of the actual public state-history marginal. -/
theorem realizedActiveOccupationStateHistoryLaw_succ
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) (initial : G.State)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (source_compatible :
      ∀ stage history index,
        selection stage history index ≠ 0 →
          germ.playerNeutralOccupationSource who index.1 =
            history (Fin.last stage))
    (stage : ℕ) :
    realizedActiveOccupationStateHistoryLaw
        germ ht who initial active selection (stage + 1) =
      (realizedActiveOccupationStateHistoryLaw
        germ ht who initial active selection stage).bind
        fun history =>
          (activeOccupationMixedStep
            germ ht who selection stage history).map
              (Fin.snoc history) := by
  unfold realizedActiveOccupationStateHistoryLaw
  rw [G.histDist_succ, PMF.map_bind]
  calc
    (G.histDist
        (realizedActiveOccupationProfile
          germ ht who active selection)
        initial stage).bind
        (fun history =>
          (((G.stageActionDist
              (realizedActiveOccupationProfile
                germ ht who active selection)
              history).bind
                (fun jointAction =>
                  (G.transition history.2 jointAction).bind
                    (fun successor =>
                      PMF.pure
                        ((Fin.snoc history.1
                          (history.2, jointAction), successor) :
                            G.Hist (stage + 1))))).map
            LowerValueJet.stateHistoryOfHist)) =
      (G.histDist
        (realizedActiveOccupationProfile
          germ ht who active selection)
        initial stage).bind
        (fun history =>
          (LowerValueJet.behaviorStateStep
            (realizedActiveOccupationProfile
              germ ht who active selection)
            history).map
              (Fin.snoc
                (LowerValueJet.stateHistoryOfHist history))) := by
        congr 1
        funext history
        rw [PMF.map_bind, LowerValueJet.behaviorStateStep]
        rw [PMF.map_bind]
        congr 1
        funext jointAction
        rw [PMF.map_bind]
        congr 1
        funext successor
        simp only [PMF.pure_map, Function.comp_apply]
        exact congrArg PMF.pure
          (LowerValueJet.stateHistoryOfHist_snoc
            history jointAction successor)
    _ =
      (G.histDist
        (realizedActiveOccupationProfile
          germ ht who active selection)
        initial stage).bind
        (fun history =>
          (activeOccupationMixedStep germ ht who selection stage
            (LowerValueJet.stateHistoryOfHist history)).map
              (Fin.snoc
                (LowerValueJet.stateHistoryOfHist history))) := by
        congr 1
        funext history
        rw [
          behaviorStateStep_realizedActiveOccupationProfile
            germ ht who active selection source_compatible history]
    _ =
      ((G.histDist
        (realizedActiveOccupationProfile
          germ ht who active selection)
        initial stage).map
          LowerValueJet.stateHistoryOfHist).bind
        (fun history =>
          (activeOccupationMixedStep
            germ ht who selection stage history).map
              (Fin.snoc history)) := by
        rw [PMF.bind_map]
        rfl

omit [DecidableEq G.State] in
/-- The actual state-history marginal is the adaptive history law of the
mixed active occupation kernels. -/
theorem realizedActiveOccupationStateHistoryLaw_eq_adaptiveHistoryLaw
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) (initial : G.State)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (source_compatible :
      ∀ stage history index,
        selection stage history index ≠ 0 →
          germ.playerNeutralOccupationSource who index.1 =
            history (Fin.last stage))
    (stage : ℕ) :
    realizedActiveOccupationStateHistoryLaw
        germ ht who initial active selection stage =
      adaptiveHistoryLaw
        (adaptiveMarkovStep initial
          (activeOccupationMixedStep germ ht who selection))
        (stage + 1) := by
  induction stage with
  | zero =>
      unfold realizedActiveOccupationStateHistoryLaw
      rw [G.histDist_zero, PMF.pure_map]
      rw [adaptiveHistoryLaw_succ, adaptiveHistoryLaw_zero]
      rw [PMF.pure_bind, adaptiveMarkovStep_zero, PMF.pure_map]
      exact congrArg PMF.pure
        (LowerValueJet.stateHistoryOfHist_empty initial)
  | succ stage inductionHypothesis =>
      rw [
        realizedActiveOccupationStateHistoryLaw_succ
          germ ht who initial active selection
          source_compatible stage,
        inductionHypothesis]
      rw [
        adaptiveHistoryLaw_succ
          (adaptiveMarkovStep initial
            (activeOccupationMixedStep
              germ ht who selection))
          (stage + 1)]
      rfl

/-- Realized one-step stage-plus-continuation gain over the frozen Fink
baseline, evaluated in the selected owner's coordinate. -/
def realizedActiveOccupationBellmanGainAt
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    {stage : ℕ} (history : G.Hist stage) : ℝ :=
  let profile :=
    realizedActiveOccupationProfile germ ht who active selection
  G.stageEUAt profile history who +
      expect (LowerValueJet.behaviorStateStep profile history)
        (fun successor => B successor who) -
    (G.mixedStageEU history.2
        (G.finkProfile (germ.finkPointAt ht) history.2) who +
      expect
        (G.finkStateKernel
          (germ.finkPointAt ht) history.2)
        (fun successor => B successor who))

omit [DecidableEq G.State] in
private theorem realizedActiveOccupation_stageEU_eq_selector
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (source_compatible :
      ∀ stage history index,
        selection stage history index ≠ 0 →
          germ.playerNeutralOccupationSource who index.1 =
            history (Fin.last stage))
    {stage : ℕ} (history : G.Hist stage) :
    G.stageEUAt
        (realizedActiveOccupationProfile
          germ ht who active selection)
        history who =
      expect
        (selection stage
          (LowerValueJet.stateHistoryOfHist history))
        (fun index =>
          G.mixedStageEU
            (germ.playerNeutralOccupationSource who index.1)
            (Function.update
              (G.finkProfile (germ.finkPointAt ht)
                (germ.playerNeutralOccupationSource who index.1))
              who
              (fixedOccupationActionDist germ ht who index))
            who) := by
  unfold stageEUAt realizedActiveOccupationProfile
  rw [G.stageActionDist_update_scheduledMarkovBehaviorProfile]
  unfold activeOccupationBehaviorStrategy
  rw [pmfPi_update_bind, expect_bind, expect_bind]
  apply ProbabilityMassFunction.expect_congr_on_support
  intro index index_mem
  have source_eq :
      germ.playerNeutralOccupationSource who index.1 =
        history.2 := by
    rw [← LowerValueJet.stateHistoryOfHist_last history]
    exact
      source_compatible stage
        (LowerValueJet.stateHistoryOfHist history)
        index index_mem
  simp only [mixedStageEU]
  rw [source_eq]
  rw [← expect_bind, ← pmfPi_update_bind]

omit [DecidableEq G.State] in
private theorem realizedActiveOccupation_continuation_eq_selector
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (source_compatible :
      ∀ stage history index,
        selection stage history index ≠ 0 →
          germ.playerNeutralOccupationSource who index.1 =
            history (Fin.last stage))
    {stage : ℕ} (history : G.Hist stage) :
    expect
        (LowerValueJet.behaviorStateStep
          (realizedActiveOccupationProfile
            germ ht who active selection)
          history)
        (fun successor => B successor who) =
      expect
        (selection stage
          (LowerValueJet.stateHistoryOfHist history))
        (fun index =>
          expect
            (germ.finkPlayerNeutralOccupationKernelAt
              ht who index.1)
            (fun successor => B successor who)) := by
  rw [
    behaviorStateStep_realizedActiveOccupationProfile
      germ ht who active selection source_compatible history]
  unfold activeOccupationMixedStep mixedTransitionComparison
  rw [expect_bind]

omit [DecidableEq G.State] in
/-- The actual one-step Bellman gain is exactly the selector expectation of
the moving raw player-neutral occupation charge. -/
theorem realizedActiveOccupationBellmanGainAt_eq_rawCharge
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (source_compatible :
      ∀ stage history index,
        selection stage history index ≠ 0 →
          germ.playerNeutralOccupationSource who index.1 =
            history (Fin.last stage))
    {stage : ℕ} (history : G.Hist stage) :
    realizedActiveOccupationBellmanGainAt
        germ B ht who active selection history =
      expect
        (selection stage
          (LowerValueJet.stateHistoryOfHist history))
        (fun index =>
          germ.rawPlayerNeutralOccupationCharge
            B who t index.1) := by
  dsimp only [realizedActiveOccupationBellmanGainAt]
  rw [
    realizedActiveOccupation_stageEU_eq_selector
      germ ht who active selection source_compatible history,
    realizedActiveOccupation_continuation_eq_selector
      germ B ht who active selection source_compatible history]
  rw [← expect_add]
  rw [←
    expect_const
      (selection stage
        (LowerValueJet.stateHistoryOfHist history))
      (G.mixedStageEU history.2
          (G.finkProfile (germ.finkPointAt ht) history.2) who +
        expect
          (G.finkStateKernel
            (germ.finkPointAt ht) history.2)
          (fun successor => B successor who))]
  rw [← expect_sub]
  apply ProbabilityMassFunction.expect_congr_on_support
  intro index index_mem
  have source_eq :
      germ.playerNeutralOccupationSource who index.1 =
        history.2 := by
    rw [← LowerValueJet.stateHistoryOfHist_last history]
    exact
      source_compatible stage
        (LowerValueJet.stateHistoryOfHist history)
        index index_mem
  rw [germ.rawPlayerNeutralOccupationCharge_eq_finkPointAt
    B ht who index.1]
  rcases index with ⟨index, membership⟩
  cases index with
  | inl source =>
      change source = history.2 at source_eq
      rw [← source_eq]
      simp only [fixedOccupationActionDist,
        playerNeutralOccupationSource]
      rw [Function.update_eq_self]
      simp only [finkPlayerNeutralOccupationKernelAt,
        playerNeutralOccupationIndexEmbedding,
        finkActualOccupationKernelAt, occupationKernel]
      ring
  | inr response =>
      change response.1.1 = history.2 at source_eq
      rw [← source_eq]
      simp only [fixedOccupationActionDist,
        playerNeutralOccupationSource,
        ContinuationNeutralAction.source]
      rw [G.finkContinuationGain_eq_expect_stateKernels]
      simp only [finkPlayerNeutralOccupationKernelAt,
        playerNeutralOccupationIndexEmbedding,
        finkActualOccupationKernelAt, occupationKernel]
      unfold finkStageGain
      rw [show response.source = response.1.1 from rfl]
      ring

/-- The fixed-epoch punctured-potential estimate now applies to the public
state-history marginal of an actual behavior strategy. -/
theorem
    AnalyticScaledChargedOccupationPotential.expected_realizedActiveCharge_le
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
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
            (germ.puncturedPlayerNeutralPotentialAt B who P t)
            index)
    (initial : G.State)
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (source_compatible :
      ∀ stage history index,
        selection stage history index ≠ 0 →
          germ.playerNeutralOccupationSource who index.1 =
            history (Fin.last stage))
    (T : ℕ) :
    expect
        (realizedActiveOccupationStateHistoryLaw
          germ ht who initial active selection T)
        (mixedTransitionCostSum selection
          (fun index =>
            germ.rawPlayerNeutralOccupationCharge
              B who t index.1) T) ≤
      2 * finiteStatePotentialBound
        (germ.puncturedPlayerNeutralPotentialAt B who P t) := by
  rw [
    realizedActiveOccupationStateHistoryLaw_eq_adaptiveHistoryLaw
      germ ht who initial active selection source_compatible T]
  exact expected_activeCharge_le
    germ B who P active ht hcharge initial selection
      source_compatible T

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
