/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.InvisiblePlayerOwnedDeviationBoundary

/-!
# Marginal recurrence for the scheduled Fink profile

The generic moving-kernel occupation account consumes a sequence of state
laws satisfying an exact one-step `PMF.bind` recurrence.  The scheduled Fink
profile is defined on full public histories, so this recurrence is not
definitionally visible at its state marginal.

This file gives the narrow bridge.  It names the epoch-frozen Fink state
kernel and the actual prescribed state marginal, identifies that marginal
with `calendarStateDist`, and exposes its exact recurrence.  No stationarity,
recurrence-class, or target-transport assertion is made.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Math Math.OnlineLearning Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- The Fink state kernel frozen at one epoch of the shifted universal
calendar. -/
def scheduledFinkEpochStateKernel
    (germ : G.AnalyticBellmanGerm)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius)
    (epoch : ℕ) : G.State → PMF G.State :=
  G.finkStateKernel (germ.finkPointAt (valid epoch))

/-- The actual state marginal under prescribed scheduled Fink play. -/
def scheduledFinkStateLaw
    (germ : G.AnalyticBellmanGerm)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius)
    (initial : G.State)
    (stage : ℕ) : PMF G.State :=
  (G.histDist
      (G.scheduledMarkovBehaviorProfile
        (fun currentStage source =>
          G.finkProfile
            (germ.finkPointAt
              (valid (anytimeEpochIndex currentStage)))
            source))
      initial stage).map Prod.snd

omit [DecidableEq G.State] in
/-- The actual prescribed state marginal is the calendar-kernel law. -/
theorem scheduledFinkStateLaw_eq_calendarStateDist
    (germ : G.AnalyticBellmanGerm)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius)
    (initial : G.State)
    (stage : ℕ) :
    scheduledFinkStateLaw germ startEpoch valid initial stage =
      calendarStateDist
        (fun currentStage =>
          scheduledFinkEpochStateKernel germ startEpoch valid
            (anytimeEpochIndex currentStage))
        initial stage := by
  exact
    map_snd_histDist_scheduledFink_eq_calendarStateDist
      germ startEpoch valid initial stage

omit [DecidableEq G.State] in
/-- Exact marginal-law recurrence for prescribed scheduled Fink play.

This is the hypothesis shape used by
`Math.Probability.exists_sublinearMovingKernelCostAccount`, with
`law := scheduledFinkStateLaw germ startEpoch valid initial` and
`kernel := scheduledFinkEpochStateKernel germ startEpoch valid`. -/
theorem scheduledFinkStateLaw_succ
    (germ : G.AnalyticBellmanGerm)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius)
    (initial : G.State)
    (stage : ℕ) :
    scheduledFinkStateLaw germ startEpoch valid initial (stage + 1) =
      (scheduledFinkStateLaw germ startEpoch valid initial stage).bind
        (scheduledFinkEpochStateKernel germ startEpoch valid
          (anytimeEpochIndex stage)) := by
  rw [scheduledFinkStateLaw_eq_calendarStateDist,
    scheduledFinkStateLaw_eq_calendarStateDist]
  rfl

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
