/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib

/-!
# Witness switching under simultaneous stopping-law perturbations

Separate stopping-law tangent columns do not in general upper-bound the
coordinatewise debt change under a simultaneous perturbation.  The obstruction
is not a multiaffine cross term: it already occurs for the maximum of two
affine deviation charts.

The fixed envelope below is the elementary quitting-game chart

`max 0 (q_left + q_right - q_blocker)`.

It can be read as one observer choosing between Never, worth zero, and
Quit-now, whose reward is `+1` when the left opponent joins, `+1` when the
right opponent joins, and `-1` when the blocker joins.  Thus the three
variables are opponent stopping masses, not a changing reward table.

At the triangular source `(0, 0, lambda)`, each of the two separate changes
of size `lambda` merely closes the blocker moat.  Neither changes the
envelope.  Applying both changes activates Quit-now and raises the envelope
by exactly `lambda`.  Hence the discrepancy is first order even though every
underlying chart is affine and uniformly bounded on the relevant cube.

Consequently, a balanced combination of separately extracted debt tangents
does not by itself produce a co-realized flat simultaneous path when the
source varies toward a best-response handoff.  A valid simultaneous-reset
argument needs either a common active-deviation passport with `o(lambda)`
switching slack, or an explicit positive witness-switch charge branch.
-/

namespace GameTheory

open scoped BigOperators

/-- The affine chart belonging to the newly activated deviation. -/
def simultaneousMixtureSwitchChart (left right blocker : ℝ) : ℝ :=
  left + right - blocker

/-- The best-response envelope of the zero chart and the switch chart. -/
def simultaneousMixtureSwitchEnvelope (left right blocker : ℝ) : ℝ :=
  max 0 (simultaneousMixtureSwitchChart left right blocker)

/-- The switch chart has no bilinear interaction between the two moved
coordinates.  In particular, the regression below cannot be charged to a
multiaffine cross term. -/
theorem simultaneousMixtureSwitchChart_additive_increment
    (left right blocker deltaLeft deltaRight : ℝ) :
    simultaneousMixtureSwitchChart (left + deltaLeft) (right + deltaRight)
        blocker -
      simultaneousMixtureSwitchChart left right blocker =
    deltaLeft + deltaRight := by
  simp only [simultaneousMixtureSwitchChart]
  ring

/-- At a blocker moat of width `lambda`, either separate perturbation only
reaches the best-response handoff, whereas their simultaneous application
crosses it by `lambda`. -/
theorem simultaneousMixtureSwitchEnvelope_triangular_values
    (lambda : ℝ) (hlambda : 0 < lambda) :
    simultaneousMixtureSwitchEnvelope 0 0 lambda = 0 ∧
      simultaneousMixtureSwitchEnvelope lambda 0 lambda = 0 ∧
      simultaneousMixtureSwitchEnvelope 0 lambda lambda = 0 ∧
      simultaneousMixtureSwitchEnvelope lambda lambda lambda = lambda := by
  simp only [simultaneousMixtureSwitchEnvelope,
    simultaneousMixtureSwitchChart]
  simp [hlambda.le]

/-- The proposed coordinatewise first-order subadditivity against separately
measured increments is false. -/
theorem not_simultaneousMixtureSwitchEnvelope_subadditive_at_moving_source
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ¬ (simultaneousMixtureSwitchEnvelope lambda lambda lambda -
          simultaneousMixtureSwitchEnvelope 0 0 lambda ≤
        (simultaneousMixtureSwitchEnvelope lambda 0 lambda -
          simultaneousMixtureSwitchEnvelope 0 0 lambda) +
        (simultaneousMixtureSwitchEnvelope 0 lambda lambda -
          simultaneousMixtureSwitchEnvelope 0 0 lambda)) := by
  obtain ⟨hsource, hleft, hright, hboth⟩ :=
    simultaneousMixtureSwitchEnvelope_triangular_values lambda hlambda
  rw [hsource, hleft, hright, hboth]
  linarith

/-- Any error term repairing the false simultaneous-versus-separate
inequality must be at least `lambda`.  Therefore no uniform `o(lambda)`
remainder can repair it along a triangular sequence of moving sources. -/
theorem simultaneousMixtureSwitchEnvelope_subadditivity_error_ge
    (lambda error : ℝ) (hlambda : 0 < lambda)
    (hcomparison :
      simultaneousMixtureSwitchEnvelope lambda lambda lambda -
          simultaneousMixtureSwitchEnvelope 0 0 lambda ≤
        (simultaneousMixtureSwitchEnvelope lambda 0 lambda -
          simultaneousMixtureSwitchEnvelope 0 0 lambda) +
        (simultaneousMixtureSwitchEnvelope 0 lambda lambda -
          simultaneousMixtureSwitchEnvelope 0 0 lambda) + error) :
    lambda ≤ error := by
  obtain ⟨hsource, hleft, hright, hboth⟩ :=
    simultaneousMixtureSwitchEnvelope_triangular_values lambda hlambda
  rw [hsource, hleft, hright, hboth] at hcomparison
  linarith

/-- The two separately normalized envelope increments vanish, but the
simultaneous normalized increment is exactly one.  This is the precise
triangular-array failure of the desired tangent inequality. -/
theorem simultaneousMixtureSwitchEnvelope_normalized_gap
    (lambda : ℝ) (hlambda : 0 < lambda) :
    (simultaneousMixtureSwitchEnvelope lambda 0 lambda -
          simultaneousMixtureSwitchEnvelope 0 0 lambda) / lambda = 0 ∧
      (simultaneousMixtureSwitchEnvelope 0 lambda lambda -
          simultaneousMixtureSwitchEnvelope 0 0 lambda) / lambda = 0 ∧
      (simultaneousMixtureSwitchEnvelope lambda lambda lambda -
          simultaneousMixtureSwitchEnvelope 0 0 lambda) / lambda = 1 := by
  obtain ⟨hsource, hleft, hright, hboth⟩ :=
    simultaneousMixtureSwitchEnvelope_triangular_values lambda hlambda
  rw [hsource, hleft, hright, hboth]
  norm_num [hlambda.ne']

/-- On the relevant triangular cube the envelope is uniformly bounded by
`lambda`; the first-order discrepancy is not caused by unbounded charts. -/
theorem simultaneousMixtureSwitchEnvelope_le_lambda
    (lambda left right blocker : ℝ)
    (hlambda : 0 ≤ lambda)
    (_hleft0 : 0 ≤ left) (hleft1 : left ≤ lambda)
    (_hright0 : 0 ≤ right) (hright1 : right ≤ lambda)
    (hblocker : lambda ≤ blocker) :
    simultaneousMixtureSwitchEnvelope left right blocker ≤ lambda := by
  unfold simultaneousMixtureSwitchEnvelope simultaneousMixtureSwitchChart
  rw [max_le_iff]
  constructor
  · exact hlambda
  · linarith

end GameTheory
