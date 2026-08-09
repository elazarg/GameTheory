/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOrbitLimit

/-!
# The all-Continue Nash--Bellman self-loop at the orbit limit

This module completes the limit geometry of arbitrary infinite exact
punishment-floor Nash--Bellman orbits inside a quitting counterexample
regime with one quantitative and one structural result.

Quantitatively, the annotations' total coordinatewise variation is
uniformly bounded.  Each one-stage increment is at most twice the reward
bound times the stage's absorption mass, so every partial variation sum
is at most twice the reward bound times the corresponding partial
absorption sum, and every partial absorption sum is bounded by the
regime's common prefix-charge budget.  The total variation of every
value coordinate is therefore at most twice the reward bound times that
one budget.

Structurally, the coordinatewise limit of the annotations is a literal
fixed point of the exact Nash--Bellman edge relation: pairing the limit
vector with the all-Continue simplex root yields a state carrying one
exact edge from itself to itself.  The Bellman conjunct holds because
the all-Continue successor payoff is the identity on continuation
vectors.  The exact endpoint-Nash conjunct reduces at the all-Continue
root to solo-reward domination, which the limit already satisfies
because the one-shot quit deviation survives passage to the limit.  The
phantom continuation target of a hypothetical counterexample is thus an
exact all-Continue self-loop, individually rational above the
behavioral punishment floor and dominating every player's solo quitting
reward.

The values are prescribed Bellman annotations, not realized payoffs of
any strategy profile.  No claim is made that the limit payoff is
achieved by play; identifying annotations with realized continuation
payoffs is precisely the separate realization problem.
-/

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingCounterexampleRegime

/-- Quantitative total variation: along every arbitrary infinite exact
punishment-floor orbit, each value coordinate's total absolute increment
is at most twice the reward bound times the regime's common
prefix-charge budget. -/
theorem infiniteOrbit_tsum_abs_value_succ_sub_le
    (regime : QuittingCounterexampleRegime reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) (who : ι) :
    ∑' time, |orbit.value (time + 1) who - orbit.value time who| ≤
      2 * quittingRewardBound reward *
        quittingPunishmentFloorPrefixChargeBound reward := by
  have h2M : (0 : ℝ) ≤ 2 * quittingRewardBound reward := by
    linarith [quittingRewardBound_nonneg reward]
  apply Real.tsum_le_of_sum_range_le (fun time => abs_nonneg _)
  intro horizon
  calc
    ∑ time ∈ Finset.range horizon,
        |orbit.value (time + 1) who - orbit.value time who| ≤
      ∑ time ∈ Finset.range horizon,
        2 * quittingRewardBound reward *
          quittingRootAbsorptionMass (orbit.roots time) :=
        Finset.sum_le_sum fun time _ =>
          orbit.abs_value_succ_sub_le_two_mul_absorptionMass time who
    _ = 2 * quittingRewardBound reward *
        orbit.partialAbsorption horizon := by
        simp only [QuittingPunishmentFloorInfiniteOrbit.partialAbsorption,
          Finset.mul_sum]
    _ ≤ 2 * quittingRewardBound reward *
        quittingPunishmentFloorPrefixChargeBound reward :=
        mul_le_mul_of_nonneg_left
          (regime.infiniteOrbit_partialAbsorption_le_prefixChargeBound
            orbit horizon) h2M

/-- **All-Continue Nash--Bellman self-loop at the limit.**  Along every
arbitrary infinite exact punishment-floor orbit of a counterexample
regime, the coordinatewise limit of the Bellman annotations, paired with
the all-Continue simplex root, carries an exact Nash--Bellman edge from
itself to itself.  The limit lies in the canonical compact reward box
and dominates the behavioral punishment floor; the exact endpoint-Nash
conjunct of the self-loop encodes that it also dominates every player's
solo quitting reward.

The annotations are prescribed Bellman values, not realized payoffs of
any strategy profile; no realization claim is made about the limit or
its self-loop. -/
theorem infiniteOrbit_exists_selfLoop_limit
    (regime : QuittingCounterexampleRegime reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) :
    ∃ limit : Payoff ι,
      (∀ who, Tendsto (fun time => orbit.value time who) atTop
        (nhds (limit who))) ∧
      limit ∈ quittingPunishmentFloorForwardCarrier reward ∧
      (∀ who, quittingPunishmentValue reward who ≤ limit who) ∧
      IsQuittingNashBellmanEdge reward
        (limit, quittingAllContinueSimplexRoot)
        (limit, quittingAllContinueSimplexRoot) := by
  obtain ⟨limit, hlimit, hcarrier, hfloor, hsolo⟩ :=
    regime.infiniteOrbit_exists_value_limit orbit
  refine ⟨limit, hlimit, hcarrier, hfloor, ?_⟩
  constructor
  · change limit = quittingRootSuccessorPayoff reward limit
      (quittingRootOfSimplex quittingAllContinueSimplexRoot)
    rw [quittingRootOfSimplex_allContinueSimplexRoot,
      quittingRootSuccessorPayoff_allContinueRoot_eq]
  · change IsεQuittingRootEndpointNash reward limit 0
      (quittingRootOfSimplex quittingAllContinueSimplexRoot)
    rw [quittingRootOfSimplex_allContinueSimplexRoot,
      isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
    exact quittingAllContinueRoot_isZeroNash_of_singleton_le reward limit
      hsolo

end QuittingCounterexampleRegime

end GameTheory
