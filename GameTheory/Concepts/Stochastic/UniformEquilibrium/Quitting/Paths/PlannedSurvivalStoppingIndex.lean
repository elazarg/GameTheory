/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Paths.BehaviorStoppingLaw

/-!
# The planned-survival stopping index

Simon (Adv. Appl. Math. 38 (2007) 1-26), Proposition 3, punishes a deviating
player off **two** per-player stopping times: a cumulative-ledger clock, and
a **planned-survival** clock `i^n_♯` -- the first stage at which the
player's own *prescribed* continuation probability
`c_i^n := ∏_{k<i} (1 − p_k^n)` has fallen to or below a target threshold
`ε/M`.  The point of this second clock is that it needs no statistical test
at all: `c_i^n` is computed from the prescribed hazard sequence alone,
before any play happens, so a player still observed live past `i^n_♯` is
*provably* off the prescribed path -- mere presence is the certificate,
not a realized-history statistic.

This file isolates that deterministic stopping index for the planned
survival curve `quittingHazardSurvival`, already defined in
`QuittingBehaviorStoppingLaw.lean` for an arbitrary Boolean hazard sequence
and, via `quittingBehaviorLiveHazard`, for an arbitrary (possibly
history-dependent) behavior strategy read along a quitting game's unique
live public history.

This is a standalone piece of Proposition 3's punishment design: a
definition and its defining inequalities, with **no capping theorem**
attached.  Proposition 3's actual content -- bounding a deviator's gain once
the trigger fires, via a rank-1 decision-discrepancy-process argument -- is
separate, larger work and is not attempted here.

## Main definitions

* `quittingPlannedSurvivalStoppingIndex` -- the first stage at which a
  planned (prescribed, history-free) survival curve drops to or below a
  threshold, or `0` if it never does
* `quittingBehaviorPlannedSurvivalStoppingIndex` -- the same index read off
  an arbitrary behavior strategy's live-path hazard sequence

## Main results

* `quittingHazardSurvival_stoppingIndex_le` -- survival is at or below the
  threshold at the stopping index
* `threshold_lt_quittingHazardSurvival_of_lt_stoppingIndex` -- survival is
  strictly above the threshold at every earlier stage (the "first crossing"
  property)
* `quittingHazardSurvival_le_of_stoppingIndex_le` -- survival stays at or
  below the threshold from the stopping index on
-/

noncomputable section

namespace GameTheory

/-- The first stage at which a planned (prescribed) survival curve drops to
or below `threshold`, or `0` if it never does.  Applied to
`c_i^n = quittingHazardSurvival hazard i` with `threshold = ε / M`, this is
Simon's stopping time `i^n_♯`: the point past which the prescribed plan
already has the player gone with probability at least `1 − ε/M`. -/
noncomputable def quittingPlannedSurvivalStoppingIndex
    (hazard : ℕ → PMF Bool) (threshold : ℝ) : ℕ := by
  classical
  exact
    if hexists : ∃ n, quittingHazardSurvival hazard n ≤ threshold then
      Nat.find hexists
    else 0

/-- At the stopping index, planned survival is at or below the threshold. -/
theorem quittingHazardSurvival_stoppingIndex_le
    (hazard : ℕ → PMF Bool) (threshold : ℝ)
    (hexists : ∃ n, quittingHazardSurvival hazard n ≤ threshold) :
    quittingHazardSurvival hazard
        (quittingPlannedSurvivalStoppingIndex hazard threshold) ≤
      threshold := by
  unfold quittingPlannedSurvivalStoppingIndex
  rw [dif_pos hexists]
  exact Nat.find_spec hexists

/-- Before the stopping index, planned survival is still strictly above the
threshold: `quittingPlannedSurvivalStoppingIndex` is the *first* crossing. -/
theorem threshold_lt_quittingHazardSurvival_of_lt_stoppingIndex
    (hazard : ℕ → PMF Bool) (threshold : ℝ)
    (hexists : ∃ n, quittingHazardSurvival hazard n ≤ threshold)
    {stage : ℕ}
    (hstage : stage < quittingPlannedSurvivalStoppingIndex hazard threshold) :
    threshold < quittingHazardSurvival hazard stage := by
  unfold quittingPlannedSurvivalStoppingIndex at hstage
  rw [dif_pos hexists] at hstage
  exact not_le.mp (Nat.find_min hexists hstage)

/-- Planned survival is antitone, so once the trigger has fired it stays
fired: from the stopping index on, survival remains at or below the
threshold. -/
theorem quittingHazardSurvival_le_of_stoppingIndex_le
    (hazard : ℕ → PMF Bool) (threshold : ℝ)
    (hexists : ∃ n, quittingHazardSurvival hazard n ≤ threshold)
    {stage : ℕ}
    (hstage : quittingPlannedSurvivalStoppingIndex hazard threshold ≤ stage) :
    quittingHazardSurvival hazard stage ≤ threshold :=
  (antitone_quittingHazardSurvival hazard hstage).trans
    (quittingHazardSurvival_stoppingIndex_le hazard threshold hexists)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The planned-survival stopping index of an arbitrary (possibly
history-dependent) behavior strategy in a quitting game, read along its
unique live public history.  Well defined for every strategy: the strategy
need not be history-independent for `i^n_♯` to make sense, only the
pre-absorption history it is evaluated along is canonical. -/
noncomputable def quittingBehaviorPlannedSurvivalStoppingIndex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {who : ι} (strategy : (quittingGame reward).BehaviorStrategy who)
    (threshold : ℝ) : ℕ :=
  quittingPlannedSurvivalStoppingIndex
    (quittingBehaviorLiveHazard reward strategy) threshold

omit [DecidableEq ι] in
/-- At a behavior strategy's planned-survival stopping index, its live-path
survival is at or below the threshold. -/
theorem quittingBehaviorLiveHazard_survival_stoppingIndex_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {who : ι} (strategy : (quittingGame reward).BehaviorStrategy who)
    (threshold : ℝ)
    (hexists : ∃ n,
      quittingHazardSurvival
        (quittingBehaviorLiveHazard reward strategy) n ≤ threshold) :
    quittingHazardSurvival (quittingBehaviorLiveHazard reward strategy)
        (quittingBehaviorPlannedSurvivalStoppingIndex reward strategy
          threshold) ≤
      threshold :=
  quittingHazardSurvival_stoppingIndex_le
    (quittingBehaviorLiveHazard reward strategy) threshold hexists

end GameTheory
