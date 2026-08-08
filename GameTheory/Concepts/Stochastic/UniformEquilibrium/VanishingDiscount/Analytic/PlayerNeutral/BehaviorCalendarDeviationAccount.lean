/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.BehaviorCalendarAccount
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.BehaviorDeviationPartition

/-!
# Calendar accounts for endpoint-neutral behavior deviations

An actual unilateral behavior strategy induces a full-history selector on
the complete player-neutral occupation family by pushing its current action
distribution through the endpoint neutral-action embedding.  If every
supported action is endpoint-neutral, realization of that selector is
exactly the original deviation against the scheduled Fink opponents.

Consequently the one-law punctured-potential calendar account applies
directly to every such behavior deviation.  Strict actions and payoff caps
remain outside this module.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Math Math.Probability Set
open Math.OnlineLearning
open Math.Probability.AnalyticScaledChargedOccupationPotential
open AnalyticScaledChargedOccupationPotential

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- Full-history occupation selector induced by a genuine unilateral
behavior strategy. -/
def fullHistoryEndpointNeutralShadowSelection
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (dev : G.BehaviorStrategy who) :
    ∀ stage, G.Hist stage →
      PMF
        {index : germ.PlayerNeutralOccupationIndex who //
          index ∈ (Finset.univ :
            Finset (germ.PlayerNeutralOccupationIndex who))} :=
  fun stage history =>
    germ.fullEndpointNeutralShadowSelection
      history.2 who (dev stage history)

omit [DecidableEq G.State] in
/-- The full-history shadow selector always remains in the current source
fiber. -/
theorem fullHistoryEndpointNeutralShadowSelection_source_compatible
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (dev : G.BehaviorStrategy who) :
    ∀ stage history index,
      germ.fullHistoryEndpointNeutralShadowSelection
          who dev stage history index ≠ 0 →
        germ.playerNeutralOccupationSource who index.1 =
          history.2 := by
  intro stage history index index_mem
  exact
    germ.fullEndpointNeutralShadowSelection_source_compatible
      history.2 who (dev stage history) index index_mem

/-- The actual unilateral deviation against the moving Fink calendar. -/
def scheduledFinkDeviationProfile
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who) :
    G.BehaviorProfile :=
  Function.update
    (G.scheduledMarkovBehaviorProfile
      (fun stage source =>
        G.finkProfile
          (germ.finkPointAt
            (valid (anytimeEpochIndex stage)))
          source))
    who dev

omit [DecidableEq G.State] in
/-- Under support-neutrality, realizing the full-history shadow selector
recovers the original owner strategy exactly. -/
theorem calendarOccupationBehaviorStrategy_shadow_eq
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    (support_neutral :
      ∀ stage history action,
        dev stage history action ≠ 0 →
          G.finkContinuationGain germ.endpointValue
            germ.endpointFinkPoint history.2 who action = 0) :
    calendarOccupationBehaviorStrategy germ who
        (Finset.univ :
          Finset (germ.PlayerNeutralOccupationIndex who))
        startEpoch valid
        (germ.fullHistoryEndpointNeutralShadowSelection who dev) =
      dev := by
  funext stage history
  unfold calendarOccupationBehaviorStrategy
    fullHistoryEndpointNeutralShadowSelection
    fullEndpointNeutralShadowSelection
    endpointNeutralShadowSelection
  rw [PMF.bind_map, PMF.bind_map]
  calc
    (dev stage history).bind
        (fun action =>
          fixedOccupationActionDist germ
            (valid (anytimeEpochIndex stage)) who
            ⟨germ.endpointNeutralShadowIndex
                history.2 who action,
              Finset.mem_univ _⟩) =
      (dev stage history).bind PMF.pure := by
        apply ProbabilityMassFunction.bind_congr_on_support
        intro action action_mem
        have action_ne_zero :
            dev stage history action ≠ 0 :=
          (PMF.mem_support_iff
            (dev stage history) action).1 action_mem
        have neutral :=
          support_neutral stage history action action_ne_zero
        simp only [endpointNeutralShadowIndex, dif_pos neutral,
          fixedOccupationActionDist]
    _ = dev stage history := PMF.bind_pure _

omit [DecidableEq G.State] in
/-- The calendar occupation realization is the actual unilateral deviation
profile whenever the deviation support is endpoint-neutral. -/
theorem realizedCalendarOccupationProfile_shadow_eq
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    (support_neutral :
      ∀ stage history action,
        dev stage history action ≠ 0 →
          G.finkContinuationGain germ.endpointValue
            germ.endpointFinkPoint history.2 who action = 0) :
    realizedCalendarOccupationProfile germ who
        (Finset.univ :
          Finset (germ.PlayerNeutralOccupationIndex who))
        startEpoch valid
        (germ.fullHistoryEndpointNeutralShadowSelection who dev) =
      scheduledFinkDeviationProfile
        germ who startEpoch valid dev := by
  unfold realizedCalendarOccupationProfile
    scheduledFinkDeviationProfile
  rw [
    germ.calendarOccupationBehaviorStrategy_shadow_eq
      who startEpoch valid dev support_neutral]

/-- Expected moving endpoint-neutral charge of an actual unilateral
behavior strategy under its own scheduled-Fink history law. -/
def expectedEndpointNeutralBehaviorCalendarCharge
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    (initial : G.State) (T : ℕ) : ℝ :=
  ∑ stage ∈ Finset.range T,
    G.expectedHistoryValue
      (scheduledFinkDeviationProfile
        germ who startEpoch valid dev)
      initial
      (fun stage history =>
        expect (dev stage history)
          (germ.endpointNeutralMovingCharge B
            (playerNeutralCalendarScale startEpoch stage)
            history.2 who))
      stage

omit [DecidableEq G.State] in
/-- For a support-neutral deviation, the realized selector charge is exactly
the charge evaluated under the actual unilateral-deviation history law. -/
theorem expectedRealizedCalendarOccupationCharge_shadow_eq
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    (support_neutral :
      ∀ stage history action,
        dev stage history action ≠ 0 →
          G.finkContinuationGain germ.endpointValue
            germ.endpointFinkPoint history.2 who action = 0)
    (initial : G.State) (T : ℕ) :
    expectedRealizedCalendarOccupationCharge germ B who
        startEpoch valid
        (germ.fullHistoryEndpointNeutralShadowSelection who dev)
        initial T =
      expectedEndpointNeutralBehaviorCalendarCharge
        germ B who startEpoch valid dev initial T := by
  have profile_eq :=
    germ.realizedCalendarOccupationProfile_shadow_eq
      who startEpoch valid dev support_neutral
  unfold expectedRealizedCalendarOccupationCharge
    expectedEndpointNeutralBehaviorCalendarCharge
  apply Finset.sum_congr rfl
  intro stage _
  unfold expectedHistoryValue
  rw [profile_eq]
  apply congrArg
  funext history
  exact germ.expect_fullEndpointNeutralShadowSelection_charge
    B (playerNeutralCalendarScale startEpoch stage)
      history.2 who (dev stage history)

/-- Every endpoint-neutral unilateral behavior deviation has an honest
sublinear moving raw-charge account under its own full public history law. -/
theorem
    AnalyticScaledChargedOccupationPotential.exists_neutralBehaviorCalendarAccount
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)) :
    ∃ (startEpoch : ℕ)
        (valid :
          ∀ k : ℕ,
            shiftedUniversalEpochScale startEpoch k ∈
              Ioo (0 : ℝ) germ.radius),
      ∀ (dev : G.BehaviorStrategy who),
        (∀ stage history action,
          dev stage history action ≠ 0 →
            G.finkContinuationGain germ.endpointValue
              germ.endpointFinkPoint history.2 who action = 0) →
        ∀ initial T,
          expectedEndpointNeutralBehaviorCalendarCharge
              germ B who startEpoch valid dev initial T ≤
            shiftedPuncturedPotentialCalendarBudget
              germ B who P startEpoch T ∧
          IsAsymptoticallySublinear
            (shiftedPuncturedPotentialCalendarBudget
              germ B who P startEpoch) := by
  obtain ⟨startEpoch, valid, account⟩ :=
    AnalyticScaledChargedOccupationPotential.exists_realizedCalendarOccupationAccount
      germ B who P
      (Finset.univ :
        Finset (germ.PlayerNeutralOccupationIndex who))
  refine ⟨startEpoch, valid, ?_⟩
  intro dev support_neutral initial T
  have source_compatible :=
    germ.fullHistoryEndpointNeutralShadowSelection_source_compatible
      who dev
  have bound :=
    account
      (germ.fullHistoryEndpointNeutralShadowSelection who dev)
      source_compatible initial T
  rw [
    germ.expectedRealizedCalendarOccupationCharge_shadow_eq
      B who startEpoch valid dev support_neutral initial T]
    at bound
  exact bound

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
