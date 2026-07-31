/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PlayerNeutralOccupationBehaviorRealization

/-!
# One-law calendar accounts for player-neutral behavior

This file realizes a changing-parameter player-neutral occupation selector
as one behavior profile on full public histories.  The analytic parameter is
frozen during each epoch of the universal quadratic calendar and changes at
the deterministic epoch boundaries.

Unlike the independently presented epoch laws in
`PlayerNeutralPuncturedPotentialCalendarAccount`, the expectation below is
taken under one actual root history law.  The selector may depend on the full
public history, including past actions.  Within each epoch the corresponding
punctured state potential telescopes under that same law; summing the
completed epochs and the current prefix gives the existing sublinear
calendar budget.

This is only a neutral-family charge account.  It does not classify strict
actions, bound a payoff, or construct a punishment certificate.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Math Math.PMFProduct Math.Probability Set
open Math.OnlineLearning
open Math.Probability.AnalyticScaledChargedOccupationPotential
open AnalyticScaledChargedOccupationPotential

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- The shifted universal parameter used at one calendar stage. -/
def playerNeutralCalendarScale
    (startEpoch stage : ℕ) : ℝ :=
  shiftedUniversalEpochScale startEpoch (anytimeEpochIndex stage)

/-- The owner strategy obtained by realizing a full-history predictable
occupation selector at the parameter of the current calendar epoch. -/
def calendarOccupationBehaviorStrategy
    (germ : G.AnalyticBellmanGerm)
    (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (selection :
      ∀ stage, G.Hist stage →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active}) :
    G.BehaviorStrategy who :=
  fun stage history =>
    (selection stage history).bind
      (fixedOccupationActionDist germ
        (valid (anytimeEpochIndex stage)) who)

/-- One actual behavior profile which follows the changing Fink calendar
except for the selected owner's player-neutral occupation mixture. -/
def realizedCalendarOccupationProfile
    (germ : G.AnalyticBellmanGerm)
    (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (selection :
      ∀ stage, G.Hist stage →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active}) :
    G.BehaviorProfile :=
  Function.update
    (G.scheduledMarkovBehaviorProfile
      (fun stage source =>
        G.finkProfile
          (germ.finkPointAt
            (valid (anytimeEpochIndex stage)))
          source))
    who
    (calendarOccupationBehaviorStrategy
      germ who active startEpoch valid selection)

/-- Selector mixture of the moving occupation kernels at one calendar
history. -/
def calendarOccupationMixedStep
    (germ : G.AnalyticBellmanGerm)
    (who : ι)
    {active : Finset (germ.PlayerNeutralOccupationIndex who)}
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (selection :
      ∀ stage, G.Hist stage →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    {stage : ℕ} (history : G.Hist stage) :
    PMF G.State :=
  (selection stage history).bind fun index =>
    germ.finkPlayerNeutralOccupationKernelAt
      (valid (anytimeEpochIndex stage)) who index.1

omit [DecidableEq G.State] in
/-- Exact one-step realization for a selector which may depend on the full
public history. -/
theorem behaviorStateStep_realizedCalendarOccupationProfile
    (germ : G.AnalyticBellmanGerm)
    (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
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
        (realizedCalendarOccupationProfile
          germ who active startEpoch valid selection)
        history =
      calendarOccupationMixedStep
        germ who startEpoch valid selection history := by
  unfold LowerValueJet.behaviorStateStep
    realizedCalendarOccupationProfile
  rw [G.stageActionDist_update_scheduledMarkovBehaviorProfile]
  unfold calendarOccupationBehaviorStrategy
    calendarOccupationMixedStep
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
    germ (valid (anytimeEpochIndex stage)) who index

/-- Moving raw occupation charge evaluated by the full-history selector of
the actual calendar profile. -/
def calendarRawOccupationCharge
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    {active : Finset (germ.PlayerNeutralOccupationIndex who)}
    (startEpoch : ℕ)
    (selection :
      ∀ stage, G.Hist stage →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active}) :
    G.HistoryPotential :=
  fun stage history =>
    expect (selection stage history) fun index =>
      germ.rawPlayerNeutralOccupationCharge B who
        (playerNeutralCalendarScale startEpoch stage) index.1

/-- The punctured state potential used during one calendar epoch. -/
def calendarEpochOccupationPotential
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (startEpoch k : ℕ) :
    G.HistoryPotential :=
  fun _ history =>
    germ.puncturedPlayerNeutralPotentialAt B who P
      (shiftedUniversalEpochScale startEpoch k) history.2

/-- At every history, the selected moving raw charge is dominated by the
actual one-step drift of the current epoch potential. -/
theorem calendarRawOccupationCharge_le_epochPotentialDrift
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
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
    (hcharge :
      ∀ k index,
        germ.rawPlayerNeutralOccupationCharge B who
            (shiftedUniversalEpochScale startEpoch k) index.1 ≤
          transitionPotentialDrift
            (fun activeIndex =>
              germ.finkPlayerNeutralOccupationKernelAt
                (valid k) who activeIndex.1)
            (fun activeIndex =>
              germ.playerNeutralOccupationSource who activeIndex.1)
            (germ.puncturedPlayerNeutralPotentialAt B who P
              (shiftedUniversalEpochScale startEpoch k))
            (index :
              {index : germ.PlayerNeutralOccupationIndex who //
                index ∈ active}))
    {stage : ℕ} (history : G.Hist stage) :
    calendarRawOccupationCharge
        germ B who startEpoch selection stage history ≤
      G.historyContinuationEU
          (realizedCalendarOccupationProfile
            germ who active startEpoch valid selection)
          (calendarEpochOccupationPotential
            germ B who P startEpoch (anytimeEpochIndex stage))
          history -
        calendarEpochOccupationPotential
          germ B who P startEpoch
            (anytimeEpochIndex stage) stage history := by
  let selector := selection stage history
  let k := anytimeEpochIndex stage
  let C : G.State → ℝ :=
    germ.puncturedPlayerNeutralPotentialAt B who P
      (shiftedUniversalEpochScale startEpoch k)
  calc
    calendarRawOccupationCharge
          germ B who startEpoch selection stage history =
        expect selector fun index =>
          germ.rawPlayerNeutralOccupationCharge B who
            (shiftedUniversalEpochScale startEpoch k) index.1 := by
      rfl
    _ ≤
        expect selector fun index =>
          transitionPotentialDrift
            (fun activeIndex =>
              germ.finkPlayerNeutralOccupationKernelAt
                (valid k) who activeIndex.1)
            (fun activeIndex =>
              germ.playerNeutralOccupationSource who activeIndex.1)
            C index :=
      expect_mono selector _ _ (hcharge k)
    _ =
        expect selector (fun index =>
          expect
              (germ.finkPlayerNeutralOccupationKernelAt
                (valid k) who index.1)
              C -
            C history.2) := by
      apply ProbabilityMassFunction.expect_congr_on_support
      intro index index_mem
      unfold transitionPotentialDrift
      change
        expect
            (germ.finkPlayerNeutralOccupationKernelAt
              (valid k) who index.1)
            C -
          C (germ.playerNeutralOccupationSource who index.1) =
        expect
            (germ.finkPlayerNeutralOccupationKernelAt
              (valid k) who index.1)
            C -
          C history.2
      rw [source_compatible stage history index index_mem]
    _ =
        expect selector (fun index =>
          expect
            (germ.finkPlayerNeutralOccupationKernelAt
              (valid k) who index.1)
            C) -
          C history.2 := by
      rw [expect_sub, expect_const]
    _ =
        expect
            (LowerValueJet.behaviorStateStep
              (realizedCalendarOccupationProfile
                germ who active startEpoch valid selection)
              history)
            C -
          C history.2 := by
      rw [
        behaviorStateStep_realizedCalendarOccupationProfile
          germ who active startEpoch valid selection
            source_compatible history]
      unfold calendarOccupationMixedStep
      rw [expect_bind]
    _ =
        G.historyContinuationEU
            (realizedCalendarOccupationProfile
              germ who active startEpoch valid selection)
            (calendarEpochOccupationPotential
              germ B who P startEpoch k)
            history -
          calendarEpochOccupationPotential
            germ B who P startEpoch k stage history := by
      unfold historyContinuationEU LowerValueJet.behaviorStateStep
        calendarEpochOccupationPotential
      rw [expect_bind]

/-- Expected raw charge at a stage is bounded by the increment of the
punctured potential of that stage's epoch, under the same root history law. -/
theorem expected_calendarRawOccupationCharge_le_epochPotentialIncrement
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
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
    (hcharge :
      ∀ k index,
        germ.rawPlayerNeutralOccupationCharge B who
            (shiftedUniversalEpochScale startEpoch k) index.1 ≤
          transitionPotentialDrift
            (fun activeIndex =>
              germ.finkPlayerNeutralOccupationKernelAt
                (valid k) who activeIndex.1)
            (fun activeIndex =>
              germ.playerNeutralOccupationSource who activeIndex.1)
            (germ.puncturedPlayerNeutralPotentialAt B who P
              (shiftedUniversalEpochScale startEpoch k))
            (index :
              {index : germ.PlayerNeutralOccupationIndex who //
                index ∈ active}))
    (initial : G.State) (stage : ℕ) :
    G.expectedHistoryValue
        (realizedCalendarOccupationProfile
          germ who active startEpoch valid selection)
        initial
        (calendarRawOccupationCharge
          germ B who startEpoch selection)
        stage ≤
      G.expectedHistoryValue
          (realizedCalendarOccupationProfile
            germ who active startEpoch valid selection)
          initial
          (calendarEpochOccupationPotential
            germ B who P startEpoch (anytimeEpochIndex stage))
          (stage + 1) -
        G.expectedHistoryValue
          (realizedCalendarOccupationProfile
            germ who active startEpoch valid selection)
          initial
          (calendarEpochOccupationPotential
            germ B who P startEpoch (anytimeEpochIndex stage))
          stage := by
  let profile :=
    realizedCalendarOccupationProfile
      germ who active startEpoch valid selection
  let raw :=
    calendarRawOccupationCharge
      germ B who startEpoch selection
  let value :=
    calendarEpochOccupationPotential
      germ B who P startEpoch (anytimeEpochIndex stage)
  rw [G.expectedHistoryValue_succ]
  unfold expectedHistoryValue
  rw [← expect_sub]
  exact expect_mono (G.histDist profile initial stage) _ _
    (calendarRawOccupationCharge_le_epochPotentialDrift
      germ B who P active startEpoch valid selection
        source_compatible hcharge)

private theorem expected_calendarEpochOccupationPotential_upper
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (selection :
      ∀ stage, G.Hist stage →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (initial : G.State) (k stage : ℕ) :
    G.expectedHistoryValue
        (realizedCalendarOccupationProfile
          germ who active startEpoch valid selection)
        initial
        (calendarEpochOccupationPotential
          germ B who P startEpoch k)
        stage ≤
      finiteStatePotentialBound
        (germ.puncturedPlayerNeutralPotentialAt B who P
          (shiftedUniversalEpochScale startEpoch k)) := by
  unfold expectedHistoryValue calendarEpochOccupationPotential
  calc
    expect
        (G.histDist
          (realizedCalendarOccupationProfile
            germ who active startEpoch valid selection)
          initial stage)
        (fun history =>
          germ.puncturedPlayerNeutralPotentialAt B who P
            (shiftedUniversalEpochScale startEpoch k) history.2) ≤
      expect
        (G.histDist
          (realizedCalendarOccupationProfile
            germ who active startEpoch valid selection)
          initial stage)
        (fun _ =>
          finiteStatePotentialBound
            (germ.puncturedPlayerNeutralPotentialAt B who P
              (shiftedUniversalEpochScale startEpoch k))) := by
        apply expect_mono
        intro history
        have habs :
            |germ.puncturedPlayerNeutralPotentialAt B who P
                (shiftedUniversalEpochScale startEpoch k) history.2| ≤
              finiteStatePotentialBound
                (germ.puncturedPlayerNeutralPotentialAt B who P
                  (shiftedUniversalEpochScale startEpoch k)) := by
          simpa [statePotentialAccount] using
            abs_statePotentialAccount_le_finiteStatePotentialBound
              (germ.puncturedPlayerNeutralPotentialAt B who P
                (shiftedUniversalEpochScale startEpoch k))
              (fun _ => history.2) 0
        exact (le_abs_self _).trans habs
    _ =
        finiteStatePotentialBound
          (germ.puncturedPlayerNeutralPotentialAt B who P
            (shiftedUniversalEpochScale startEpoch k)) := by
      rw [expect_const]

private theorem expected_calendarEpochOccupationPotential_lower
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (selection :
      ∀ stage, G.Hist stage →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (initial : G.State) (k stage : ℕ) :
    -finiteStatePotentialBound
        (germ.puncturedPlayerNeutralPotentialAt B who P
          (shiftedUniversalEpochScale startEpoch k)) ≤
      G.expectedHistoryValue
        (realizedCalendarOccupationProfile
          germ who active startEpoch valid selection)
        initial
        (calendarEpochOccupationPotential
          germ B who P startEpoch k)
        stage := by
  unfold expectedHistoryValue calendarEpochOccupationPotential
  calc
    -finiteStatePotentialBound
          (germ.puncturedPlayerNeutralPotentialAt B who P
            (shiftedUniversalEpochScale startEpoch k)) =
      expect
        (G.histDist
          (realizedCalendarOccupationProfile
            germ who active startEpoch valid selection)
          initial stage)
        (fun _ =>
          -finiteStatePotentialBound
            (germ.puncturedPlayerNeutralPotentialAt B who P
              (shiftedUniversalEpochScale startEpoch k))) := by
        rw [expect_const]
    _ ≤
      expect
        (G.histDist
          (realizedCalendarOccupationProfile
            germ who active startEpoch valid selection)
          initial stage)
        (fun history =>
          germ.puncturedPlayerNeutralPotentialAt B who P
            (shiftedUniversalEpochScale startEpoch k) history.2) := by
        apply expect_mono
        intro history
        have habs :
            |germ.puncturedPlayerNeutralPotentialAt B who P
                (shiftedUniversalEpochScale startEpoch k) history.2| ≤
              finiteStatePotentialBound
                (germ.puncturedPlayerNeutralPotentialAt B who P
                  (shiftedUniversalEpochScale startEpoch k)) := by
          simpa [statePotentialAccount] using
            abs_statePotentialAccount_le_finiteStatePotentialBound
              (germ.puncturedPlayerNeutralPotentialAt B who P
                (shiftedUniversalEpochScale startEpoch k))
              (fun _ => history.2) 0
        exact neg_le_of_abs_le habs

/-- Every prefix of one epoch has expected raw charge bounded by that
epoch's full punctured-potential bill under the actual global history law. -/
theorem expected_calendarOccupationEpochCharge_le
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
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
    (hcharge :
      ∀ k index,
        germ.rawPlayerNeutralOccupationCharge B who
            (shiftedUniversalEpochScale startEpoch k) index.1 ≤
          transitionPotentialDrift
            (fun activeIndex =>
              germ.finkPlayerNeutralOccupationKernelAt
                (valid k) who activeIndex.1)
            (fun activeIndex =>
              germ.playerNeutralOccupationSource who activeIndex.1)
            (germ.puncturedPlayerNeutralPotentialAt B who P
              (shiftedUniversalEpochScale startEpoch k))
            (index :
              {index : germ.PlayerNeutralOccupationIndex who //
                index ∈ active}))
    (initial : G.State) (k horizon : ℕ)
    (hhorizon : horizon ≤ anytimeEpochLength k) :
    ∑ offset ∈ Finset.range horizon,
        G.expectedHistoryValue
          (realizedCalendarOccupationProfile
            germ who active startEpoch valid selection)
          initial
          (calendarRawOccupationCharge
            germ B who startEpoch selection)
          (epochStart anytimeEpochLength k + offset) ≤
      shiftedPuncturedPotentialEpochBudget
        germ B who P startEpoch k := by
  let profile :=
    realizedCalendarOccupationProfile
      germ who active startEpoch valid selection
  let raw :=
    calendarRawOccupationCharge
      germ B who startEpoch selection
  let value :=
    calendarEpochOccupationPotential
      germ B who P startEpoch k
  let start := epochStart anytimeEpochLength k
  have hindex (offset : ℕ) (hoffset : offset < horizon) :
      anytimeEpochIndex (start + offset) = k := by
    apply anytimeEpochIndex_eq
    · exact Nat.le_add_right start offset
    · rw [epochStart_succ]
      omega
  have hstep (offset : ℕ) (hoffset : offset < horizon) :
      G.expectedHistoryValue profile initial raw
          (start + offset) ≤
        G.expectedHistoryValue profile initial value
            (start + offset + 1) -
          G.expectedHistoryValue profile initial value
            (start + offset) := by
    have h :=
      expected_calendarRawOccupationCharge_le_epochPotentialIncrement
        germ B who P active startEpoch valid selection
          source_compatible hcharge initial (start + offset)
    simpa only [hindex offset hoffset, profile, raw, value] using h
  calc
    ∑ offset ∈ Finset.range horizon,
          G.expectedHistoryValue profile initial raw
            (start + offset) ≤
        ∑ offset ∈ Finset.range horizon,
          (G.expectedHistoryValue profile initial value
              (start + offset + 1) -
            G.expectedHistoryValue profile initial value
              (start + offset)) := by
      apply Finset.sum_le_sum
      intro offset hoffset
      exact hstep offset (Finset.mem_range.mp hoffset)
    _ =
        G.expectedHistoryValue profile initial value
            (start + horizon) -
          G.expectedHistoryValue profile initial value start := by
      let f : ℕ → ℝ :=
        fun offset =>
          G.expectedHistoryValue profile initial value
            (start + offset)
      have htelescope := Finset.sum_range_sub' f horizon
      have hneg :
          (∑ offset ∈ Finset.range horizon,
              (f (offset + 1) - f offset)) =
            -(∑ offset ∈ Finset.range horizon,
              (f offset - f (offset + 1))) := by
        calc
          (∑ offset ∈ Finset.range horizon,
              (f (offset + 1) - f offset)) =
            ∑ offset ∈ Finset.range horizon,
              -(f offset - f (offset + 1)) := by
                apply Finset.sum_congr rfl
                intro offset _
                ring
          _ =
            -(∑ offset ∈ Finset.range horizon,
              (f offset - f (offset + 1))) :=
                Finset.sum_neg_distrib _
      change
        (∑ offset ∈ Finset.range horizon,
            (f (offset + 1) - f offset)) =
          f horizon - f 0
      rw [hneg, htelescope]
      dsimp only [f]
      ring
    _ ≤
        2 * finiteStatePotentialBound
          (germ.puncturedPlayerNeutralPotentialAt B who P
            (shiftedUniversalEpochScale startEpoch k)) := by
      have hupper :=
        expected_calendarEpochOccupationPotential_upper
          germ B who P active startEpoch valid selection
            initial k (start + horizon)
      have hlower :=
        expected_calendarEpochOccupationPotential_lower
          germ B who P active startEpoch valid selection
            initial k start
      change
        G.expectedHistoryValue profile initial value
              (start + horizon) -
            G.expectedHistoryValue profile initial value start ≤
          2 * finiteStatePotentialBound
            (germ.puncturedPlayerNeutralPotentialAt B who P
              (shiftedUniversalEpochScale startEpoch k))
      linarith
    _ =
        shiftedPuncturedPotentialEpochBudget
          germ B who P startEpoch k := by
      rfl

private theorem expected_calendarOccupationCompletedCharge_le
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
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
    (hcharge :
      ∀ k index,
        germ.rawPlayerNeutralOccupationCharge B who
            (shiftedUniversalEpochScale startEpoch k) index.1 ≤
          transitionPotentialDrift
            (fun activeIndex =>
              germ.finkPlayerNeutralOccupationKernelAt
                (valid k) who activeIndex.1)
            (fun activeIndex =>
              germ.playerNeutralOccupationSource who activeIndex.1)
            (germ.puncturedPlayerNeutralPotentialAt B who P
              (shiftedUniversalEpochScale startEpoch k))
            (index :
              {index : germ.PlayerNeutralOccupationIndex who //
                index ∈ active}))
    (initial : G.State) (K : ℕ) :
    ∑ stage ∈ Finset.range (epochStart anytimeEpochLength K),
        G.expectedHistoryValue
          (realizedCalendarOccupationProfile
            germ who active startEpoch valid selection)
          initial
          (calendarRawOccupationCharge
            germ B who startEpoch selection)
          stage ≤
      ∑ k ∈ Finset.range K,
        shiftedPuncturedPotentialEpochBudget
          germ B who P startEpoch k := by
  induction K with
  | zero =>
      simp [epochStart]
  | succ K inductionHypothesis =>
      rw [epochStart_succ, Finset.sum_range_add,
        Finset.sum_range_succ]
      exact add_le_add inductionHypothesis
        (expected_calendarOccupationEpochCharge_le
          germ B who P active startEpoch valid selection
            source_compatible hcharge initial K
            (anytimeEpochLength K) le_rfl)

/-- Cumulative expected moving raw charge under one actual changing-parameter
behavior profile and its full public history law. -/
def expectedRealizedCalendarOccupationCharge
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    {active : Finset (germ.PlayerNeutralOccupationIndex who)}
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (selection :
      ∀ stage, G.Hist stage →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (initial : G.State) (T : ℕ) : ℝ :=
  ∑ stage ∈ Finset.range T,
    G.expectedHistoryValue
      (realizedCalendarOccupationProfile
        germ who active startEpoch valid selection)
      initial
      (calendarRawOccupationCharge
        germ B who startEpoch selection)
      stage

/-- The one-law expected calendar charge is bounded by the same
completed-plus-current punctured-potential budget as the local epoch
accounts. -/
theorem expectedRealizedCalendarOccupationCharge_le_budget
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
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
    (hcharge :
      ∀ k index,
        germ.rawPlayerNeutralOccupationCharge B who
            (shiftedUniversalEpochScale startEpoch k) index.1 ≤
          transitionPotentialDrift
            (fun activeIndex =>
              germ.finkPlayerNeutralOccupationKernelAt
                (valid k) who activeIndex.1)
            (fun activeIndex =>
              germ.playerNeutralOccupationSource who activeIndex.1)
            (germ.puncturedPlayerNeutralPotentialAt B who P
              (shiftedUniversalEpochScale startEpoch k))
            (index :
              {index : germ.PlayerNeutralOccupationIndex who //
                index ∈ active}))
    (initial : G.State) (T : ℕ) :
    expectedRealizedCalendarOccupationCharge
        germ B who startEpoch valid selection initial T ≤
      shiftedPuncturedPotentialCalendarBudget
        germ B who P startEpoch T := by
  let K := anytimeEpochIndex T
  let offset := anytimeEpochOffset T
  have htime :
      epochStart anytimeEpochLength K + offset = T := by
    exact anytimeEpochStart_add_offset T
  unfold expectedRealizedCalendarOccupationCharge
    shiftedPuncturedPotentialCalendarBudget
    completedAndCurrentEpochBudget
  change
    (∑ stage ∈ Finset.range T,
      G.expectedHistoryValue
        (realizedCalendarOccupationProfile
          germ who active startEpoch valid selection)
        initial
        (calendarRawOccupationCharge
          germ B who startEpoch selection)
        stage) ≤
      (∑ k ∈ Finset.range K,
        shiftedPuncturedPotentialEpochBudget
          germ B who P startEpoch k) +
        shiftedPuncturedPotentialEpochBudget
          germ B who P startEpoch K
  rw [← htime, Finset.sum_range_add]
  apply add_le_add
  · exact expected_calendarOccupationCompletedCharge_le
      germ B who P active startEpoch valid selection
        source_compatible hcharge initial K
  · exact expected_calendarOccupationEpochCharge_le
      germ B who P active startEpoch valid selection
        source_compatible hcharge initial K offset
        (anytimeEpochOffset_le T)

/-- Every scaled occupation potential supplies an honest sublinear expected
charge account for one full-history predictable neutral behavior calendar. -/
theorem
    AnalyticScaledChargedOccupationPotential.exists_realizedCalendarOccupationAccount
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (active : Finset (germ.PlayerNeutralOccupationIndex who)) :
    ∃ (startEpoch : ℕ)
        (valid :
          ∀ k : ℕ,
            shiftedUniversalEpochScale startEpoch k ∈
              Ioo (0 : ℝ) germ.radius),
      ∀ (selection :
          ∀ stage, G.Hist stage →
            PMF
              {index : germ.PlayerNeutralOccupationIndex who //
                index ∈ active}),
        (∀ stage history index,
          selection stage history index ≠ 0 →
            germ.playerNeutralOccupationSource who index.1 =
              history.2) →
        ∀ initial T,
          expectedRealizedCalendarOccupationCharge
              germ B who startEpoch valid selection initial T ≤
            shiftedPuncturedPotentialCalendarBudget
              germ B who P startEpoch T ∧
          IsAsymptoticallySublinear
            (shiftedPuncturedPotentialCalendarBudget
              germ B who P startEpoch) := by
  obtain ⟨startEpoch, valid, hcharge⟩ :=
    exists_startEpoch_activeCharge_le_drift
      germ B who P active
  refine ⟨startEpoch, valid, ?_⟩
  intro selection source_compatible initial T
  exact
    ⟨expectedRealizedCalendarOccupationCharge_le_budget
        germ B who P active startEpoch valid selection
          source_compatible hcharge initial T,
      shiftedPuncturedPotentialCalendarBudget_sublinear
        germ B who P startEpoch⟩

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
