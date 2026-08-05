/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingUnboundedInverseIterate
import GameTheory.Concepts.Stochastic.QuittingBellmanTelescope
import GameTheory.Concepts.Stochastic.QuittingCycleMismatchContraction

/-!
# The survival-prefix bridge

The survival-prefix notion has two forms with no lemma relating them before
this file:

* the **full-product** form `quittingSurvivalPrefix rows N =
  ∏ t < N, quittingStationaryContinueMass (rows t)`
  (`QuittingUnboundedInverseIterate.lean`), the joint probability that every
  player continues at every one of the first `N` stages, used for complete
  absorption;
* the **deleted-product** form `quittingOpponentSurvivalWeight roots who
  start fuel = ∏ offset < fuel, quittingFixedOpponentsContinueMass roots who
  (start + offset)` (`QuittingBellmanTelescope.lean`), the probability that
  every *opponent* of `who` continues, used throughout the isolated-coordinate
  case split (`QuittingCycleIsolatedCoordinate.lean`,
  `QuittingRelaxedCycleGain.lean`).

The bridge is exactly what factoring `who`'s own coordinate out of the joint
product gives: at a single root, the joint continue mass is the deleted
(opponents-only) continue mass times `who`'s own continue probability
(`quittingStationaryContinueMass_eq_deletedContinueMass_mul_own`). Lifting
this pointwise identity across a finite prefix via `Finset.prod_mul_distrib`
gives the prefix-level bridge
(`quittingSurvivalPrefix_eq_opponentSurvivalWeight_mul_own`): the full survival
prefix is the opponent survival weight times the prefix of `who`'s own
continue probabilities. Without this, translating a complete-absorption fact
stated on `quittingSurvivalPrefix` into an opponent-survival-weight statement
(as the isolated-coordinate case split needs) has no shortcut and must be
re-derived by hand at each use site.

This file is deliberately thin: it imports both sides
(`QuittingUnboundedInverseIterate.lean` for the full-product form,
`QuittingBellmanTelescope.lean` and `QuittingCycleMismatchContraction.lean`
for the deleted-product form) so that any file consuming either side can also
consume the bridge without an extra import of its own.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The pointwise bridge.** The joint (full-product) continue mass at a
single root factors as the deleted (opponents-only) continue mass times
`who`'s own continue probability. -/
theorem quittingStationaryContinueMass_eq_deletedContinueMass_mul_own
    (root : ι → PMF Bool) (who : ι) :
    quittingStationaryContinueMass root =
      quittingRootDeletedContinueMass root who * (root who false).toReal := by
  classical
  have hdeleted : quittingRootDeletedContinueMass root who =
      ∏ player ∈ Finset.univ.erase who, (root player false).toReal := by
    rw [quittingRootDeletedContinueMass, quittingStationaryContinueMass_eq_prod_continueProbability,
      ← Finset.mul_prod_erase Finset.univ
        (fun player => (Function.update root who (PMF.pure false) player false).toReal)
        (Finset.mem_univ who)]
    have hown : (Function.update root who (PMF.pure false) who false).toReal = 1 := by
      simp
    rw [hown, one_mul]
    refine Finset.prod_congr rfl fun player hplayer ↦ ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hplayer)]
  rw [quittingStationaryContinueMass_eq_prod_continueProbability, hdeleted,
    ← Finset.mul_prod_erase Finset.univ (fun player => (root player false).toReal)
      (Finset.mem_univ who)]
  ring

/-- **The prefix-level bridge.** The full-product survival prefix over the
first `N` stages equals the deleted-product opponent survival weight over the
same stages times the prefix of `who`'s own continue probabilities. One line
from the pointwise bridge via `Finset.prod_mul_distrib`, as reported. -/
theorem quittingSurvivalPrefix_eq_opponentSurvivalWeight_mul_own
    (rows : ℕ → ι → PMF Bool) (who : ι) (N : ℕ) :
    quittingSurvivalPrefix rows N =
      quittingOpponentSurvivalWeight rows who 0 N *
        ∏ t ∈ Finset.range N, (rows t who false).toReal := by
  unfold quittingSurvivalPrefix quittingOpponentSurvivalWeight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun t _ ↦ ?_
  rw [quittingStationaryContinueMass_eq_deletedContinueMass_mul_own (rows t) who,
    quittingRootDeletedContinueMass_eq_fixedOpponents, zero_add]

end GameTheory
