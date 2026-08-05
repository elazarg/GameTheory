/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PlayerOwnedBehaviorCalendarAccount

/-!
# One behavior calendar for a common player-owned potential

An owner-indexed scaled charged-occupation potential has one shared
pole-clearing order.  This file also chooses one shared calendar burn-in.
Thus every player is evaluated against the same prescribed Fink schedule;
the construction does not silently choose a different calendar for each
unilateral deviation.

The resulting accounts control the moving player-owned charges.  They do
not control the prescribed Bellman residual, which is a separate payoff
interface.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Filter Math Math.OnlineLearning Math.Probability Set Topology
open Math.Probability.AnalyticScaledChargedOccupationPotential

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace CommonPlayerOwnedPotentialCalendar

/-- The owner specialization of a common scaled potential retains the
shared pole-clearing order. -/
def ownerPotential
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (P : AnalyticOwnerScaledChargedOccupationPotential
      (fun who => OwnerOccupationIndex G who)
      (fun who => germ.rawOwnerAnalyticOccupationColumn who)
      (fun who => germ.rawPlayerOwnedOccupationCharge B who))
    (who : ι) :
    AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who) where
  poleOrder := P.poleOrder
  potential := P.potential who
  analytic_potential := P.analytic_potential who
  eventual := P.eventual.mono fun _ ht index =>
    ht who index

/-- The common potential controls every player's operational family on one
punctured neighborhood. -/
theorem eventually_allPlayerOwnedCharge_le_drift
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (P : AnalyticOwnerScaledChargedOccupationPotential
      (fun who => OwnerOccupationIndex G who)
      (fun who => germ.rawOwnerAnalyticOccupationColumn who)
      (fun who => germ.rawPlayerOwnedOccupationCharge B who)) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
        ∀ who index,
          germ.rawPlayerOwnedOccupationCharge B who t index ≤
            transitionPotentialDrift
              (germ.finkOwnerActualOccupationKernelAt ht who)
              (ownerActualOccupationSource who)
              (germ.puncturedPlayerOwnedPotentialAt B who
                (ownerPotential germ B P who) t)
              index := by
  have hAll :=
    Filter.eventually_all.mpr fun who =>
      AnalyticScaledChargedOccupationPotential.eventually_playerOwnedCharge_le_drift
        germ B who (ownerPotential germ B P who)
  filter_upwards [hAll] with t ht
  intro hvalid who index
  exact ht who hvalid index

/-- One finite burn-in makes the common calendar valid and its charge
inequality true for every owner. -/
theorem exists_commonStartEpoch_playerOwnedCharge_le_drift
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (P : AnalyticOwnerScaledChargedOccupationPotential
      (fun who => OwnerOccupationIndex G who)
      (fun who => germ.rawOwnerAnalyticOccupationColumn who)
      (fun who => germ.rawPlayerOwnedOccupationCharge B who)) :
    ∃ (startEpoch : ℕ)
        (valid :
          ∀ k : ℕ,
            shiftedUniversalEpochScale startEpoch k ∈
              Ioo (0 : ℝ) germ.radius),
      ∀ who k index,
        germ.rawPlayerOwnedOccupationCharge B who
            (shiftedUniversalEpochScale startEpoch k) index ≤
          transitionPotentialDrift
            (germ.finkOwnerActualOccupationKernelAt (valid k) who)
            (ownerActualOccupationSource who)
            (germ.puncturedPlayerOwnedPotentialAt B who
              (ownerPotential germ B P who)
              (shiftedUniversalEpochScale startEpoch k))
            index := by
  have hscale :
      Tendsto universalEpochScale atTop
        (nhdsWithin 0 (Ioi (0 : ℝ))) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact
      ⟨tendsto_universalEpochScale,
        Filter.Eventually.of_forall universalEpochScale_pos⟩
  have hvalid :
      ∀ᶠ k : ℕ in atTop,
        universalEpochScale k ∈ Ioo (0 : ℝ) germ.radius :=
    hscale.eventually (Ioo_mem_nhdsGT germ.radius_pos)
  have hcharge :
      ∀ᶠ k : ℕ in atTop,
        ∀ hk :
            universalEpochScale k ∈ Ioo (0 : ℝ) germ.radius,
          ∀ who index,
            germ.rawPlayerOwnedOccupationCharge B who
                (universalEpochScale k) index ≤
              transitionPotentialDrift
                (germ.finkOwnerActualOccupationKernelAt hk who)
                (ownerActualOccupationSource who)
                (germ.puncturedPlayerOwnedPotentialAt B who
                  (ownerPotential germ B P who)
                  (universalEpochScale k))
                index :=
    hscale.eventually
      (eventually_allPlayerOwnedCharge_le_drift germ B P)
  obtain ⟨startEpoch, hstart⟩ :=
    eventually_atTop.1 (hcharge.and hvalid)
  let valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius :=
    fun k => (hstart (startEpoch + k) (by omega)).2
  refine ⟨startEpoch, valid, ?_⟩
  intro who k index
  have h :=
    (hstart (startEpoch + k) (by omega)).1
      (valid k) who index
  simpa only [shiftedUniversalEpochScale] using h

/-- A common scaled potential yields one prescribed Fink calendar for all
players.  Against that same calendar, every unilateral behavior strategy
has its owner-specific sublinear charge account. -/
theorem exists_commonPlayerOwnedBehaviorCalendarAccount
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (P : AnalyticOwnerScaledChargedOccupationPotential
      (fun who => OwnerOccupationIndex G who)
      (fun who => germ.rawOwnerAnalyticOccupationColumn who)
      (fun who => germ.rawPlayerOwnedOccupationCharge B who)) :
    ∃ (startEpoch : ℕ)
        (valid :
          ∀ k : ℕ,
            shiftedUniversalEpochScale startEpoch k ∈
              Ioo (0 : ℝ) germ.radius),
      ∀ (who : ι) (dev : G.BehaviorStrategy who) initial T,
        expectedPlayerOwnedBehaviorCalendarCharge
            germ B who startEpoch valid dev initial T ≤
          AnalyticScaledChargedOccupationPotential.playerOwnedPotentialCalendarBudget
            germ B who (ownerPotential germ B P who)
            startEpoch T ∧
        IsAsymptoticallySublinear
          (AnalyticScaledChargedOccupationPotential.playerOwnedPotentialCalendarBudget
            germ B who (ownerPotential germ B P who)
            startEpoch) := by
  obtain ⟨startEpoch, valid, hcharge⟩ :=
    exists_commonStartEpoch_playerOwnedCharge_le_drift germ B P
  refine ⟨startEpoch, valid, ?_⟩
  intro who dev initial T
  exact
    ⟨expectedPlayerOwnedBehaviorCalendarCharge_le_budget
        germ B who (ownerPotential germ B P who)
        startEpoch valid (hcharge who) dev initial T,
      AnalyticScaledChargedOccupationPotential.playerOwnedPotentialCalendarBudget_sublinear
        germ B who (ownerPotential germ B P who) startEpoch⟩

end CommonPlayerOwnedPotentialCalendar
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
