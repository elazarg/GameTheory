/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.PlayerOwned.CalendarBellmanResidual
import UniformEquilibrium.VanishingDiscount.Analytic.PlayerOwned.CommonPotentialCalendarAccount

/-!
# Payoff boundary for a common player-owned potential

The common scaled potential supplies one prescribed calendar and sublinear
unilateral charge accounts for every player.  The exact Bellman telescope
leaves one further term: the prescribed residual evaluated under the
deviating history law.

This file states that missing term as a uniform sublinear account and proves
that it is exactly enough for simultaneous eventual deviation caps.  It
does not infer the residual account from the analytic potential, and it does
not provide the separate two-sided on-path payoff estimate.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Filter Math Math.OnlineLearning Math.Probability Set
open Math.Probability.AnalyticScaledChargedOccupationPotential

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- A uniform upper account for the prescribed Bellman residual on the
common player-owned calendar.  The bound is uniform over the unilateral
behavior strategy and the initial state. -/
structure PlayerOwnedCalendarResidualAccount
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (target : Payoff ι) where
  budget : ι → ℕ → ℝ
  residual_le :
    ∀ (who : ι) (dev : G.BehaviorStrategy who) initial T,
      (∑ stage ∈ Finset.range T,
          G.expectedHistoryValue
            (scheduledPlayerOwnedFinkDeviationProfile
              germ who startEpoch valid dev)
            initial
            (playerOwnedCalendarPrescribedBellmanResidual
              germ B who startEpoch valid (target who))
            stage) ≤
        budget who T
  sublinear :
    ∀ who, IsAsymptoticallySublinear (budget who)

/-- A shared player-owned charge calendar and a sublinear residual account
give one horizon threshold for all players, initial states, and unilateral
behavior strategies. -/
theorem eventually_all_finiteAveragePayoff_playerOwnedCalendar_le_target_add
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (P : AnalyticOwnerScaledChargedOccupationPotential
      (fun who => OwnerOccupationIndex G who)
      (fun who => germ.rawOwnerAnalyticOccupationColumn who)
      (fun who => germ.rawPlayerOwnedOccupationCharge B who))
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (hcharge :
      ∀ who k index,
        germ.rawPlayerOwnedOccupationCharge B who
            (shiftedUniversalEpochScale startEpoch k) index ≤
          transitionPotentialDrift
            (germ.finkOwnerActualOccupationKernelAt (valid k) who)
            (ownerActualOccupationSource who)
            (germ.puncturedPlayerOwnedPotentialAt B who
              (CommonPlayerOwnedPotentialCalendar.ownerPotential
                germ B P who)
              (shiftedUniversalEpochScale startEpoch k))
            index)
    (target : Payoff ι)
    (residual :
      PlayerOwnedCalendarResidualAccount
        germ B startEpoch valid target)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℕ in atTop,
      ∀ (who : ι) (dev : G.BehaviorStrategy who) initial,
        G.finiteAveragePayoff initial T
            (scheduledPlayerOwnedFinkDeviationProfile
              germ who startEpoch valid dev)
            who ≤
          target who + δ := by
  have hwho (who : ι) :
      ∀ᶠ T : ℕ in atTop,
        ∀ (dev : G.BehaviorStrategy who) initial,
          G.finiteAveragePayoff initial T
              (scheduledPlayerOwnedFinkDeviationProfile
                germ who startEpoch valid dev)
              who ≤
            target who + δ := by
    let ownerPotential :=
      CommonPlayerOwnedPotentialCalendar.ownerPotential
        germ B P who
    let chargeBudget : ℕ → ℝ :=
      AnalyticScaledChargedOccupationPotential.playerOwnedPotentialCalendarBudget
        germ B who ownerPotential startEpoch
    let totalBudget : ℕ → ℝ := fun T =>
      2 * finiteStatePotentialBound (fun state => B state who) +
        chargeBudget T + residual.budget who T
    have htotal : IsAsymptoticallySublinear totalBudget := by
      apply IsAsymptoticallySublinear.add
      · apply IsAsymptoticallySublinear.add
        · exact IsAsymptoticallySublinear.const
            (2 * finiteStatePotentialBound
              (fun state => B state who))
        · exact
            AnalyticScaledChargedOccupationPotential.playerOwnedPotentialCalendarBudget_sublinear
              germ B who ownerPotential startEpoch
      · exact residual.sublinear who
    filter_upwards
        [htotal.eventually_average_le hδ,
          eventually_gt_atTop 0] with T haverage hT
    intro dev initial
    have hchargeBound :
        expectedPlayerOwnedBehaviorCalendarCharge
            germ B who startEpoch valid dev initial T ≤
          chargeBudget T := by
      simpa only [chargeBudget, ownerPotential] using
        expectedPlayerOwnedBehaviorCalendarCharge_le_budget
          germ B who ownerPotential startEpoch valid
          (hcharge who) dev initial T
    have hcap :=
      finiteAveragePayoff_playerOwnedCalendar_le_target_add
        germ B who startEpoch valid (target who)
        (chargeBudget T) (residual.budget who T)
        dev initial
        hchargeBound
        (residual.residual_le who dev initial T) hT
    calc
      G.finiteAveragePayoff initial T
            (scheduledPlayerOwnedFinkDeviationProfile
              germ who startEpoch valid dev)
            who ≤
          target who + totalBudget T / (T : ℝ) := by
        simpa only [totalBudget, chargeBudget, ownerPotential] using hcap
      _ =
          target who + (T : ℝ)⁻¹ * totalBudget T := by
        rw [div_eq_mul_inv, mul_comm]
      _ ≤ target who + δ :=
        by
          simpa only [add_comm] using
            add_le_add_left haverage (target who)
  have hAll : ∀ᶠ T : ℕ in atTop, ∀ who, ∀ dev initial,
      G.finiteAveragePayoff initial T
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          who ≤
        target who + δ :=
    Filter.eventually_all.mpr hwho
  exact hAll

/-- A residual account for one fixed public entry.  Uniform-equilibrium
verification requires this entry-indexed form; no control from unrelated
initial states is imposed. -/
structure PlayerOwnedCalendarResidualAccountAt
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (target : Payoff ι) where
  budget : ι → ℕ → ℝ
  residual_le :
    ∀ (who : ι) (dev : G.BehaviorStrategy who) T,
      (∑ stage ∈ Finset.range T,
          G.expectedHistoryValue
            (scheduledPlayerOwnedFinkDeviationProfile
              germ who startEpoch valid dev)
            entry
            (playerOwnedCalendarPrescribedBellmanResidual
              germ B who startEpoch valid (target who))
            stage) ≤
        budget who T
  sublinear :
    ∀ who, IsAsymptoticallySublinear (budget who)

/-- Entry-indexed residual accounts give one horizon threshold for every
player and unilateral behavior strategy from that entry. -/
theorem eventually_all_finiteAveragePayoff_playerOwnedCalendarAt_le_target_add
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (P : AnalyticOwnerScaledChargedOccupationPotential
      (fun who => OwnerOccupationIndex G who)
      (fun who => germ.rawOwnerAnalyticOccupationColumn who)
      (fun who => germ.rawPlayerOwnedOccupationCharge B who))
    (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (hcharge :
      ∀ who k index,
        germ.rawPlayerOwnedOccupationCharge B who
            (shiftedUniversalEpochScale startEpoch k) index ≤
          transitionPotentialDrift
            (germ.finkOwnerActualOccupationKernelAt (valid k) who)
            (ownerActualOccupationSource who)
            (germ.puncturedPlayerOwnedPotentialAt B who
              (CommonPlayerOwnedPotentialCalendar.ownerPotential
                germ B P who)
              (shiftedUniversalEpochScale startEpoch k))
            index)
    (target : Payoff ι)
    (residual :
      PlayerOwnedCalendarResidualAccountAt
        germ B entry startEpoch valid target)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℕ in atTop,
      ∀ (who : ι) (dev : G.BehaviorStrategy who),
        G.finiteAveragePayoff entry T
            (scheduledPlayerOwnedFinkDeviationProfile
              germ who startEpoch valid dev)
            who ≤
          target who + δ := by
  have hwho (who : ι) :
      ∀ᶠ T : ℕ in atTop,
        ∀ dev : G.BehaviorStrategy who,
          G.finiteAveragePayoff entry T
              (scheduledPlayerOwnedFinkDeviationProfile
                germ who startEpoch valid dev)
              who ≤
            target who + δ := by
    let ownerPotential :=
      CommonPlayerOwnedPotentialCalendar.ownerPotential
        germ B P who
    let chargeBudget : ℕ → ℝ :=
      AnalyticScaledChargedOccupationPotential.playerOwnedPotentialCalendarBudget
        germ B who ownerPotential startEpoch
    let totalBudget : ℕ → ℝ := fun T =>
      2 * finiteStatePotentialBound (fun state => B state who) +
        chargeBudget T + residual.budget who T
    have htotal : IsAsymptoticallySublinear totalBudget := by
      apply IsAsymptoticallySublinear.add
      · apply IsAsymptoticallySublinear.add
        · exact IsAsymptoticallySublinear.const
            (2 * finiteStatePotentialBound
              (fun state => B state who))
        · exact
            AnalyticScaledChargedOccupationPotential.playerOwnedPotentialCalendarBudget_sublinear
              germ B who ownerPotential startEpoch
      · exact residual.sublinear who
    filter_upwards
        [htotal.eventually_average_le hδ,
          eventually_gt_atTop 0] with T haverage hT
    intro dev
    have hchargeBound :
        expectedPlayerOwnedBehaviorCalendarCharge
            germ B who startEpoch valid dev entry T ≤
          chargeBudget T := by
      simpa only [chargeBudget, ownerPotential] using
        expectedPlayerOwnedBehaviorCalendarCharge_le_budget
          germ B who ownerPotential startEpoch valid
          (hcharge who) dev entry T
    have hcap :=
      finiteAveragePayoff_playerOwnedCalendar_le_target_add
        germ B who startEpoch valid (target who)
        (chargeBudget T) (residual.budget who T)
        dev entry hchargeBound
        (residual.residual_le who dev T) hT
    calc
      G.finiteAveragePayoff entry T
            (scheduledPlayerOwnedFinkDeviationProfile
              germ who startEpoch valid dev)
            who ≤
          target who + totalBudget T / (T : ℝ) := by
        simpa only [totalBudget, chargeBudget, ownerPotential] using hcap
      _ =
          target who + (T : ℝ)⁻¹ * totalBudget T := by
        rw [div_eq_mul_inv, mul_comm]
      _ ≤ target who + δ := by
        simpa only [add_comm] using
          add_le_add_left haverage (target who)
  have hAll : ∀ᶠ T : ℕ in atTop, ∀ who, ∀ dev,
      G.finiteAveragePayoff entry T
          (scheduledPlayerOwnedFinkDeviationProfile
            germ who startEpoch valid dev)
          who ≤
        target who + δ :=
    Filter.eventually_all.mpr hwho
  exact hAll

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
