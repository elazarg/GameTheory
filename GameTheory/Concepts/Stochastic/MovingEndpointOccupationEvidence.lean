/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.FiniteBiasPrescribedCalendarPayoffBoundary
import Math.Probability.MovingEndpointOccupationEvidence

/-!
# Moving endpoint transport: a fixed occupation witness

For an arbitrary sequence of state laws, cumulative transport of a fixed
endpoint target is a finite linear combination of state occupation masses.
Consequently there is an exact first reduction:

* if every state with nonzero endpoint displacement has sublinear
  occupation, then the absolute endpoint transport is sublinear;
* otherwise one fixed state and one fixed orientation have positive
  endpoint displacement and non-sublinear cumulative occupation.

The result is then instantiated with the actual state marginals of the
prescribed shifted universal Fink calendar.  It is valid for the moving,
time-inhomogeneous analytic calendar; no frozen-kernel class is inserted.

The occupation witness is deliberately weaker than a recursive child.
It does not assert that the selected state belongs to a legally closed
continuation class, preserves the whole payoff target, or decreases rank.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace MovingEndpointOccupationEvidence

open Filter Math Math.OnlineLearning Math.Probability Set
open Math.Probability.MovingEndpointOccupationEvidence

/-! ## The actual prescribed analytic calendar -/

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ who, Fintype (G.Act who)]
  [∀ who, DecidableEq (G.Act who)]

open AnalyticBellmanGerm AnalyticBellmanGerm.FiniteBiasSeed

/-- State marginal of prescribed play on the shifted universal Fink
calendar. -/
def prescribedCalendarStateLaw
    (germ : G.AnalyticBellmanGerm)
    (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius)
    (stage : ℕ) : PMF G.State :=
  (G.histDist
      (prescribedPlayerOwnedFinkCalendarProfile
        germ startEpoch valid)
      entry stage).map Prod.snd

omit [DecidableEq G.State] in
/-- The generic moving-law transport is exactly the named prescribed
calendar endpoint-transport term. -/
theorem cumulativeEndpointTransport_prescribedCalendarStateLaw
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius)
    (horizon : ℕ) :
    cumulativeEndpointTransport
        (prescribedCalendarStateLaw
          germ entry startEpoch valid)
        (fun state => germ.endpointValue state who)
        entry horizon =
      expectedPrescribedCalendarEndpointTargetTransport
        germ who entry startEpoch valid horizon := by
  unfold cumulativeEndpointTransport
    prescribedCalendarStateLaw
    expectedPrescribedCalendarEndpointTargetTransport
    expectedHistoryValue
  apply Finset.sum_congr rfl
  intro stage _
  rw [expect_map]

omit [DecidableEq G.State] in
/-- Failure of the named prescribed-calendar transport boundary for one
player exposes a fixed state and fixed orientation whose actual cumulative
occupation under that same universal calendar is non-sublinear. -/
theorem exists_prescribed_orientedOccupation_of_not_sublinear
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius)
    (failure :
      ¬IsAsymptoticallySublinear fun horizon =>
        |expectedPrescribedCalendarEndpointTargetTransport
          germ who entry startEpoch valid horizon|) :
    Nonempty
      (OrientedOccupation
        (prescribedCalendarStateLaw
          germ entry startEpoch valid)
        (fun state => germ.endpointValue state who)
        entry) := by
  apply exists_orientedOccupation_of_not_sublinear
  simpa only [
    cumulativeEndpointTransport_prescribedCalendarStateLaw] using failure

omit [DecidableEq G.State] in
/-- Therefore failure of the all-player prescribed transport boundary
selects one player and one fixed oriented non-sublinear state occupation
witness on the exact calendar used by the finite-bias closure. -/
theorem exists_player_prescribed_orientedOccupation_of_not_boundary
    (germ : G.AnalyticBellmanGerm)
    (entry : G.State)
    (startEpoch : ℕ)
    (valid :
      ∀ epoch : ℕ,
        shiftedUniversalEpochScale startEpoch epoch ∈
          Ioo (0 : ℝ) germ.radius)
    (failure :
      ¬HasSublinearPrescribedCalendarEndpointTargetTransport
        germ entry startEpoch valid) :
    ∃ who,
      Nonempty
        (OrientedOccupation
          (prescribedCalendarStateLaw
            germ entry startEpoch valid)
          (fun state => germ.endpointValue state who)
          entry) := by
  rw [HasSublinearPrescribedCalendarEndpointTargetTransport] at failure
  obtain ⟨who, hwho⟩ := not_forall.mp failure
  exact ⟨who,
    exists_prescribed_orientedOccupation_of_not_sublinear
      germ who entry startEpoch valid hwho⟩

end MovingEndpointOccupationEvidence
end StochasticGame
end GameTheory
